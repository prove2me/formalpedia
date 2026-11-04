-- Prove2me | solution 1 for ThreeSum.TernaryCoverMoments.target_bad_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:49.767461+00:00
-- url     : https://prove2.me/submissions/e4b420e5-e1ea-4983-ad57-91843199329b

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace ThreeSum.TernaryCoverMoments
theorem _root_.solution (X : Ω → T → ℕ) (k τ : ℕ) (t : T) :
    τ ^ k * (univ.filter fun w => τ < X w t).card ≤ ∑ w, X w t ^ k := by
  classical
  calc
    _ = ∑ _w ∈ (univ.filter fun w => τ < X w t), τ ^ k := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ (univ.filter fun w => τ < X w t), X w t ^ k := by
      apply sum_le_sum
      intro w hw
      exact Nat.pow_le_pow_left (mem_filter.mp hw).2.le k
    _ ≤ ∑ w, X w t ^ k :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)
end ThreeSum.TernaryCoverMoments
