-- Prove2me | solution 1 for ThreeSum.Scales.microSize_real_root_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:14.86765+00:00
-- url     : https://prove2.me/submissions/719149dc-e4da-48ed-b879-9fc26b25fa0d

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_microSize_cube_le
import Theorems.Thm_ThreeSum_Scales_cube_lt_microSize_add_three
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (m : ℕ) :
    (microSize m : ℝ) ≤ (m : ℝ) ^ (1 / 3 : ℝ) ∧
      (m : ℝ) ^ (1 / 3 : ℝ) < (microSize m : ℝ) + 3 := by
  simp only [one_div]
  constructor
  · apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg (microSize m)) (Nat.cast_nonneg m)
      (by norm_num : (0 : ℝ) < 3)).mpr
    norm_num only [Real.rpow_natCast]
    exact_mod_cast microSize_cube_le m
  · apply (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg m)
      (by positivity : (0 : ℝ) ≤ (microSize m : ℝ) + 3)
      (by norm_num : (0 : ℝ) < 3)).mpr
    norm_num only [Real.rpow_natCast]
    exact_mod_cast cube_lt_microSize_add_three m
end ThreeSum.Scales
