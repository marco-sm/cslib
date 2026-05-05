/-
Copyright (c) 2026 Marco Santamaria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco Santamaria
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Multiset.Basic

/-! # Classical Propositional Sequent Calculus (LK)

We formalise Gentzen's classical propositional sequent calculus LK, following the variant
G3cp of Negri and von Plato (§3.1). Structural rules (weakening, contraction, exchange)
are not primitive: exchange is implicit in multisets, weakening and contraction are
admissible (Negri §3.2). This presentation is deductively equivalent to Gentzen's original
LK (Troelstra, Proposition 3.5.9).

## Implementation notes

`Proposition` is defined independently of `Cslib.Logics.Propositional.Defs`, with `bot` as
an explicit constructor rather than an atom. This is required by G3cp, whose initial rule
must be restricted to genuine atoms (Negri §1.1, §2.2). We follow the pattern of
`Cslib.Logic.CLL`.

TODO: we propose to unify this definition with `Cslib.Logic.PL.Proposition` by adding
`bot` as an explicit constructor in `Defs.lean`, following the pattern of `Cslib.Logic.CLL`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][Negri2001], §2.2, §3.1
* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][Troelstra2000], §3.1, §3.5

-/

@[expose] public section

universe u

namespace Cslib.Logic.LK

/-- Propositions of classical propositional logic. -/
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  /-- Falsum, as a zero-place connective (Negri §1.1). -/
  | bot
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
  | impl (a b : Proposition Atom)
deriving DecidableEq, BEq

instance : Bot (Proposition Atom) := ⟨.bot⟩

/-- Negation as a defined connective: `¬A := A → ⊥`. -/
abbrev Proposition.neg (a : Proposition Atom) : Proposition Atom := .impl a ⊥

scoped infix:36 " ∧ " => Proposition.and
scoped infix:35 " ∨ " => Proposition.or
scoped infix:30 " → " => Proposition.impl
scoped prefix:40 " ¬ " => Proposition.neg

/-- A sequent `Γ ⊢ Δ` with antecedent and succedent as multisets of propositions. -/
structure Sequent (Atom : Type u) where
  ant : Multiset (Proposition Atom)
  suc : Multiset (Proposition Atom)

scoped notation Γ:60 " ⊢ " Δ => Sequent.mk Γ Δ

open Proposition in
inductive Proof : Sequent Atom → Type u where
  /-- Axiom rule, restricted to atoms (Negri §2.2). -/
  | ax : Proof ((atom p ::ₘ Γ) ⊢ (atom p ::ₘ Δ))
  | botL : Proof ((⊥ ::ₘ Γ) ⊢ Δ)
  | andL : Proof ((A ::ₘ B ::ₘ Γ) ⊢ Δ) → Proof (((A ∧ B) ::ₘ Γ) ⊢ Δ)
  | andR : Proof (Γ ⊢ (A ::ₘ Δ)) → Proof (Γ ⊢ (B ::ₘ Δ)) → Proof (Γ ⊢ ((A ∧ B) ::ₘ Δ))
  | orL  : Proof ((A ::ₘ Γ) ⊢ Δ) → Proof ((B ::ₘ Γ) ⊢ Δ) → Proof (((A ∨ B) ::ₘ Γ) ⊢ Δ)
  | orR  : Proof (Γ ⊢ (A ::ₘ B ::ₘ Δ)) → Proof (Γ ⊢ ((A ∨ B) ::ₘ Δ))
  | implL : Proof (Γ ⊢ (A ::ₘ Δ)) → Proof ((B ::ₘ Γ) ⊢ Δ) → Proof (((A → B) ::ₘ Γ) ⊢ Δ)
  | implR : Proof ((A ::ₘ Γ) ⊢ (B ::ₘ Δ)) → Proof (Γ ⊢ ((A → B) ::ₘ Δ))
  | cut   : Proof (Γ ⊢ (A ::ₘ Δ)) → Proof ((A ::ₘ Γ) ⊢ Δ) → Proof (Γ ⊢ Δ)

open Logic InferenceSystem

instance : HasInferenceSystem (Sequent Atom) := ⟨Proof⟩

/-- Convenience definition for rewriting conclusions in proofs. -/
@[scoped grind =]
def Proof.rwConclusion {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : ⇓Γ) :=
  InferenceSystem.rwConclusion h p

/-- A proof is cut-free if it contains no applications of the cut rule. -/
def Proof.cutFree : Proof s → Bool
  | ax | botL                      => true
  | andL p | orR p | implR p       => p.cutFree
  | andR p q | orL p q | implL p q => p.cutFree && q.cutFree
  | cut _ _                        => false

/-! ## Admissible structural rules (Negri §3.2) -/

/-- Left weakening is admissible. -/
def Proof.weakL : Proof (Γ ⊢ Δ) → Proof ((A ::ₘ Γ) ⊢ Δ)
  | @ax _ p Γ' Δ' =>
      Multiset.cons_swap A (Proposition.atom p) Γ' ▸ @ax _ p (A ::ₘ Γ') Δ'
  | @botL _ Γ' Δ' =>
      Multiset.cons_swap A (⊥ : Proposition _) Γ' ▸ @botL _ (A ::ₘ Γ') Δ'
  | @andL _ A' B' Γ' Δ' h =>
      let step1 : Proof ((A' ::ₘ A ::ₘ B' ::ₘ Γ') ⊢ Δ') :=
          Multiset.cons_swap A' A (B' ::ₘ Γ') ▸ h.weakL
      let step2 : Proof ((A' ::ₘ B' ::ₘ A ::ₘ Γ') ⊢ Δ') :=
          congrArg (A' ::ₘ ·) (Multiset.cons_swap B' A Γ') ▸ step1
      Multiset.cons_swap A (A' ∧ B') Γ' ▸ andL step2
  | andR h1 h2 => andR h1.weakL h2.weakL
  | @orL _ A' Γ' Δ' B' h1 h2 =>
      Multiset.cons_swap A (A' ∨ B') Γ' ▸
        orL (Multiset.cons_swap A' A Γ' ▸ h1.weakL)
            (Multiset.cons_swap B' A Γ' ▸ h2.weakL)
  | orR h => orR h.weakL
  | @implL _ Γ' A' Δ' B' h1 h2 =>
      Multiset.cons_swap A (A' → B') Γ' ▸
        implL h1.weakL (Multiset.cons_swap B' A Γ' ▸ h2.weakL)
  | @implR _ A' Γ' B' Δ' h =>
      implR (Multiset.cons_swap A' A Γ' ▸ h.weakL)
  | @cut _ Γ' C Δ' h1 h2 =>
      cut h1.weakL (Multiset.cons_swap C A Γ' ▸ h2.weakL)

/-- Right weakening is admissible. -/
def Proof.weakR (p : Proof (Γ ⊢ Δ)) : Proof (Γ ⊢ (A ::ₘ Δ)) := by
  sorry

/-- Left contraction is admissible. -/
def Proof.contractL (p : Proof ((A ::ₘ A ::ₘ Γ) ⊢ Δ)) : Proof ((A ::ₘ Γ) ⊢ Δ) := by
  sorry

/-- Right contraction is admissible. -/
def Proof.contractR (p : Proof (Γ ⊢ (A ::ₘ A ::ₘ Δ))) : Proof (Γ ⊢ (A ::ₘ Δ)) := by
  sorry

/-! ## Admissible rules for negation (Negri §3.1) -/

/-- Left negation rule is admissible. -/
def Proof.negL (p : Proof (Γ ⊢ (A ::ₘ Δ))) : Proof ((Proposition.neg A ::ₘ Γ) ⊢ Δ) := by
  sorry

/-- Right negation rule is admissible. -/
def Proof.negR (p : Proof ((A ::ₘ Γ) ⊢ Δ)) : Proof (Γ ⊢ (Proposition.neg A ::ₘ Δ)) := by
  sorry

/-! ## Cut elimination (Negri §3.3) -/

/-- Cut elimination: every proof can be transformed into a cut-free proof of the same sequent. -/
def Proof.cutElim (p : Proof s) : {q : Proof s // q.cutFree} := by
  sorry

end Cslib.Logic.LK
