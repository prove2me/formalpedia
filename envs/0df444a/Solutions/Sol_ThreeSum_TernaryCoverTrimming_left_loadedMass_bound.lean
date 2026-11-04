-- Prove2me | solution 1 for ThreeSum.TernaryCoverTrimming.left_loadedMass_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:26.620474+00:00
-- url     : https://prove2.me/submissions/ca92cf75-2f75-402c-ac81-4b5d17b385c2

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_loadedMass_eq
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Theorems.Thm_ThreeSum_TernaryCoverHashes_left_triple_card
import Theorems.Thm_ThreeSum_TernaryCoverHashes_pairEvent_card
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
    Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices leftVector a ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)) := by
  classical
  rw [loadedMass_eq, mul_sum]
  have hterm (u : Word (ι := ι) (K := K)) :
      Fintype.card K ^ 3 *
        ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = a).card ≤
      (if u = x then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
        Fintype.card (Weight (ι := ι) (K := K)) := by
    by_cases hu : u = x
    · subst u
      have heq : ((pairEvent x y a b).filter fun w => linearHash (leftVector x) w = a) =
          pairEvent x y a b := by
        apply filter_eq_self.mpr
        intro w hw
        exact (mem_filter.mp hw).2.1
      rw [heq, if_pos rfl]
      have hp := pairEvent_card x y a b
      have hm := congrArg (fun z : ℕ => Fintype.card K * z) hp
      nlinarith
    · rw [if_neg hu]
      simpa using (left_triple_card (Ne.symm hu) y a b a).le
  calc
    _ ≤ ∑ u ∈ vertices,
        ((if u = x then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
          Fintype.card (Weight (ι := ι) (K := K))) := sum_le_sum fun u _ => hterm u
    _ ≤ Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) +
        vertices.card * Fintype.card (Weight (ι := ι) (K := K)) := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq']
      simp only [Nat.cast_id]
      split_ifs <;> omega
    _ = _ := by ring
end ThreeSum.TernaryCoverTrimming
