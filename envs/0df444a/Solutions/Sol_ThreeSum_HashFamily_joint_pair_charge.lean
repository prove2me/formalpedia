-- Prove2me | solution 1 for ThreeSum.HashFamily.joint_pair_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:27.234073+00:00
-- url     : https://prove2.me/submissions/e2915395-82fc-4543-8335-9dc3734378d2

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_exists_coordinate_ne
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Definitions.Def_WeightedCache3SUM_Alias_1cd7057ffbb790f0
import Theorems.Thm_ThreeSum_HashFamily_jointPair_card_four
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f) (a b : K) (e f : E) :
    Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card ≤
      Fintype.card (α × Bool → K) *
        (1 + (if e = f then Fintype.card K ^ 2 else 0) +
          (if f ∈ badPartners left right e then Fintype.card K else 0)) := by
  by_cases hef : e = f
  · subst f
    have hc := pairEvent_card (hcross e e) a b
    have heq : Fintype.card K ^ 4 * (pairEvent (left e) (right e) a b).card =
        Fintype.card (α × Bool → K) * Fintype.card K ^ 2 := by
      calc
        _ = Fintype.card K ^ 2 *
            (Fintype.card K ^ 2 * (pairEvent (left e) (right e) a b).card) := by ring
        _ = _ := by rw [hc]; ring
    simp only [Finset.inter_self, ite_true, heq]
    apply Nat.mul_le_mul_left
    omega
  · have hpair : (left e, right e) ≠ (left f, right f) := fun h => hef (hinj h)
    by_cases hbad : f ∈ badPartners left right e
    · have hc := jointPair_card_le_cube (hcross e e) (hcross e f)
        (Ne.symm (hcross f e)) (hcross f f) hpair a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 3 *
            (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card) := by ring
        _ ≤ Fintype.card K * Fintype.card (α × Bool → K) := Nat.mul_le_mul_left _ hc
        _ ≤ _ := by
          simp only [if_neg hef, if_pos hbad, add_zero]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hn : left e ≠ left f ∧ right e ≠ right f ∧
          outputMask left right e ≠ outputMask left right f := by
        simpa [badPartners, not_or] using hbad
      have hm : ∃ i, (left e i == right e i) ≠ (left f i == right f i) :=
        exists_coordinate_ne hn.2.2
      have hc := jointPair_card_four (hcross e e) hn.1 (hcross e f)
        (Ne.symm (hcross f e)) hn.2.1 (hcross f f) hm a b
      simp only [if_neg hef, if_neg hbad, add_zero, mul_one, hc]
      rfl
end ThreeSum.HashFamily
