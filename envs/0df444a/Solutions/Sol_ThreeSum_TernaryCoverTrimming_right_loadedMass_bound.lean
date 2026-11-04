-- Prove2me | solution 1 for ThreeSum.TernaryCoverTrimming.right_loadedMass_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:28.245039+00:00
-- url     : https://prove2.me/submissions/4f916454-b243-43d4-847d-38a757444782

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_loadedMass_eq
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Theorems.Thm_ThreeSum_TernaryCoverHashes_pairEvent_card
import Theorems.Thm_ThreeSum_TernaryCoverHashes_right_triple_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverTrimming
theorem _root_.solution (x y : Word (ι := ι) (K := K)) (a b : K)
    (vertices : Finset (Word (ι := ι) (K := K))) :
    Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices rightVector b ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)) := by
  classical
  rw [loadedMass_eq, mul_sum]
  have hterm (u : Word (ι := ι) (K := K)) :
      Fintype.card K ^ 3 *
        ((pairEvent x y a b).filter fun w => linearHash (rightVector u) w = b).card ≤
      (if u = y then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
        Fintype.card (Weight (ι := ι) (K := K)) := by
    by_cases hu : u = y
    · subst u
      have heq : ((pairEvent x y a b).filter fun w => linearHash (rightVector y) w = b) =
          pairEvent x y a b := by
        apply filter_eq_self.mpr
        intro w hw
        exact (mem_filter.mp hw).2.2
      rw [heq, if_pos rfl]
      have hp := pairEvent_card x y a b
      have hm := congrArg (fun z : ℕ => Fintype.card K * z) hp
      nlinarith
    · rw [if_neg hu]
      simpa using (right_triple_card x (Ne.symm hu) a b b).le
  calc
    _ ≤ ∑ u ∈ vertices,
        ((if u = y then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
          Fintype.card (Weight (ι := ι) (K := K))) := sum_le_sum fun u _ => hterm u
    _ ≤ Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) +
        vertices.card * Fintype.card (Weight (ι := ι) (K := K)) := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq']
      simp only [Nat.cast_id]
      split_ifs <;> omega
    _ = _ := by ring
end ThreeSum.TernaryCoverTrimming
