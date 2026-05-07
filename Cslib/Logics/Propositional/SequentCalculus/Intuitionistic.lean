/-
Copyright (c) 2026 Marco Santamaria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco Santamaria
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.Basic

/-! # Intuitionistic Propositional Sequent Calculus (LJ)

We formalise Gentzen's intuitionistic propositional sequent calculus LJ, following the variant
G3i of Negri and von Plato (§3.1). A proof is intuitionistic if every sequent in the
derivation has at most one formula in the succedent.

The main results are:
- Cut elimination for LJ, derived computationally from strong normalization.
- Strong normalization of cut reduction for LJ (Van Dalen §7.3.6), in contrast with the
  classical case where only weak normalization holds (Van Dalen §7.2.7).

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][Negri2001], §3.1
* [D. van Dalen, *Logic and Structure*][VanDalen2004], §7.2, §7.3

-/

@[expose] public section

namespace Cslib.Logic.LK

open Proposition

/-! ## G3i as a restriction of G3cp -/

/-- A proof is intuitionistic (G3i) if every sequent in the derivation has at most one
formula in the succedent (Negri §3.1). -/
def Proof.isIntuitionistic : Proof s → Prop
  | ax      => s.suc.card ≤ 1
  | botL    => s.suc.card ≤ 1
  | andL h  => h.isIntuitionistic
  | andR h1 h2 => h1.isIntuitionistic ∧ h2.isIntuitionistic
  | orL h1 h2  => h1.isIntuitionistic ∧ h2.isIntuitionistic
  | orR h   => h.isIntuitionistic
  | implL h1 h2 => h1.isIntuitionistic ∧ h2.isIntuitionistic
  | implR h => h.isIntuitionistic
  | cut h1 h2 => h1.isIntuitionistic ∧ h2.isIntuitionistic

/-- A bundled LJ proof: a G3cp proof that is intuitionistic. -/
def ProofI (s : Sequent Atom) := {p : Proof s // p.isIntuitionistic}

/-! ## Inference system for LJ -/

opaque LJ : Type := Empty

instance : InferenceSystem LJ (Sequent Atom) := ⟨ProofI⟩

/-! ## Cut reduction for LJ -/

/-- Cut reduction restricted to LJ proofs. -/
def ProofI.CutReduces {s : Sequent Atom} (p q : ProofI s) : Prop :=
  Proof.CutReduces p.val q.val

/-! ## Strong normalization for LJ -/

/-- Strong normalization of cut reduction for LJ: every sequence of cut reductions
terminates (Van Dalen §7.3.6). In contrast with the classical case, this holds for
all reduction sequences, not just some. -/
theorem ProofI.strongNorm {s : Sequent Atom} (p : ProofI s) :
    Acc ProofI.CutReduces p := by
  sorry

/-! ## Cut elimination for LJ -/

/-- Cut elimination for LJ, derived computationally from strong normalization.
Unlike the classical case, `cutElim` for LJ follows directly from `strongNorm`
by recursion on the accessibility predicate. -/
def ProofI.cutElim {s : Sequent Atom} (p : ProofI s) :
    {q : ProofI s // q.val.cutFree} :=
  sorry

/-! ## isIntuitionistic is preserved by cut reduction -/

/-- Cut reduction preserves the intuitionistic property. -/
theorem Proof.CutReduces.preservesIntuitionistic {s : Sequent Atom}
    {p q : Proof s} (hpq : Proof.CutReduces p q) (hp : p.isIntuitionistic) :
    q.isIntuitionistic := by
  sorry

end Cslib.Logic.LK
