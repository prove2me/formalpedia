-- Prove2me | solution 1 for ThreeSum.TernaryCoverPartitionLower.three_pow_le_weighted_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:07.840021+00:00
-- url     : https://prove2.me/submissions/567ec271-894c-4981-b5f3-09a9615ba64f

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_bounds
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverPartitionLower
open BinomialEntropy LocalCoverBounds
namespace ThreeSum.TernaryCoverPartitionLower
theorem _root_.solution (s : ℕ) :
    3 ^ (3*s) ≤ (3*s+1) * (3*s).choose s * 2 ^ (2*s) := by
  by_cases hs : s = 0
  · subst s; norm_num
  have h := (weight_bounds (n := 3*s) (k := s) (by omega)).2
  have hsub : 3*s-s = 2*s := by omega
  unfold weight at h
  rw [hsub] at h
  have hn : (3*s) ^ (3*s) ≤ (3*s+1) * ((3*s).choose s * s^s * (2*s)^(2*s)) := by
    exact_mod_cast h
  have he : s^s*s^(2*s) = s^(3*s) := by rw [← pow_add]; congr 1; omega
  have ht : 3^(3*s)*s^(3*s) ≤ ((3*s+1)*(3*s).choose s*2^(2*s))*s^(3*s) := by
    calc
      _ = (3*s)^(3*s) := (mul_pow _ _ _).symm
      _ ≤ (3*s+1)*(3*s).choose s*s^s*(2*s)^(2*s) := by simpa [Nat.mul_assoc] using hn
      _ = _ := by rw [mul_pow]; rw [← he]; ring
  exact Nat.le_of_mul_le_mul_right ht (Nat.pow_pos (Nat.pos_of_ne_zero hs))
end ThreeSum.TernaryCoverPartitionLower
