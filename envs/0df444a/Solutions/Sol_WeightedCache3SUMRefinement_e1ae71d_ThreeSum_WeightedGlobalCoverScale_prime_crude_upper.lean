-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.prime_crude_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:27:55.586081+00:00
-- url     : https://prove2.me/submissions/085dd235-643e-4848-b00b-c474c65b2a95

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_prime_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_vertices_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : prime m ≤ 2^(2*fixedLength m+2) := by
  have hM := vertices_upper (fixedLength m) (fixedPi m)
  have hR : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ 3^fixedLength m := by
    have hp := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) (fixedPi m 1)
    have ht : fixedPi m 1+fixedPi m 2 ≤ fixedLength m := by have := fixedPi_total m; omega
    exact (Nat.mul_le_mul_right _ hp).trans (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) ht)
  have hs := (prime_upper m).trans (Nat.mul_le_mul_left 16 (Nat.mul_le_mul hM hR))
  have hq : prime m ≤ 4*3^fixedLength m := by nlinarith [sq_nonneg (prime m-4*3^fixedLength m : ℤ)]
  calc
    _ ≤ 4*3^fixedLength m := hq
    _ ≤ 4*(2^2)^fixedLength m := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by decide) _)
    _ = _ := by rw [← pow_mul, show (4 : ℕ) = 2^2 by norm_num, ← pow_add]; congr 1; omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
