-- Prove2me | solution 1 for Sensitivity213981Formal.MinmaxLocal.holds_iff_lt_height
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:31:01.974569+00:00
-- url     : https://prove2.me/submissions/8b0b6c92-5b3f-46c9-9177-ba90d4070c13

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_MinmaxLocal
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset


namespace Sensitivity213981Formal
section
/-
Unconditional local lemmas for the graded min/max sensitivity transfer.

This file proves actual predicates and actual one-coordinate-flip identities.
It does not assume a sensitivity-transfer theorem or a recursive seed theorem.
The exact rank is defined from the finite nested family, rather than supplied
as an unproved rank oracle.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MinmaxLocal
open scoped Classical

variable {N : ℕ} {X J I : Type}









/-- Nesting makes the true predicate indices an initial segment. -/
theorem holds_iff_lt_height (F : Fin N → X → Prop) (hF : Nested F)
    (x : X) (i : Fin N) : F i x ↔ i.val <  height F x := by
  classical
  constructor
  · intro hi
    have hh := Finset.le_sup (s := (Finset.univ : Finset (Fin N)))
      (f := fun j => if F j x then j.val + 1 else 0) (Finset.mem_univ i)
    simp only [if_pos hi] at hh
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i.val) hh
  · intro hi
    change i.val <  Finset.univ.sup (fun j : Fin N => if F j x then j.val + 1 else 0) at hi
    obtain ⟨j, _, hj⟩ := Finset.lt_sup_iff.mp hi
    by_cases htrue : F j x
    · simp only [if_pos htrue] at hj
      exact hF i j (by change i.val ≤  j.val; omega) x htrue
    · simp only [if_neg htrue] at hj
      omega

































section ActualFlips
open OAI.Paper320
variable [Fintype I]



















end ActualFlips















end MinmaxLocal










end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {N : Nat} {X : Type} (F : Fin N → X → Prop) (hF : @Sensitivity213981Formal.MinmaxLocal.Nested N X F) (x : X)
  (i : Fin N),
  Iff (F i x) (@LT.lt.{0} Nat instLTNat (@Fin.val N i) (@Sensitivity213981Formal.MinmaxLocal.height N X F x)) := @Sensitivity213981Formal.MinmaxLocal.holds_iff_lt_height
