-- Prove2me | solution 1 for ThreeSum.Scales.microSize_square_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:35.46605+00:00
-- url     : https://prove2.me/submissions/7931616d-ae2e-42eb-a9df-5cfb76badc06

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

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {m : ℕ} (hm : 0 < microSize m) :
    (microSize m : ℝ) ^ 2 / m ≤ (microSize m : ℝ)⁻¹ := by
  have hx : (0 : ℝ) < microSize m := by exact_mod_cast hm
  have hcube : (microSize m : ℝ) ^ 3 ≤ (m : ℝ) := by
    exact_mod_cast microSize_cube_le m
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hcube
  apply (div_le_iff₀ hmpos).mpr
  rw [mul_comm ((microSize m : ℝ)⁻¹) (m : ℝ)]
  change (microSize m : ℝ) ^ 2 ≤ (m : ℝ) / microSize m
  apply (le_div_iff₀ hx).mpr
  nlinarith [hcube]
end ThreeSum.Scales
