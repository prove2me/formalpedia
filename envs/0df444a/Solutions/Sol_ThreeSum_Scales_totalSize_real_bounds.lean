-- Prove2me | solution 1 for ThreeSum.Scales.totalSize_real_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:22.532712+00:00
-- url     : https://prove2.me/submissions/4d2fc090-60e9-42cb-89fc-b597dd3d1fcc

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
import Theorems.Thm_ThreeSum_Scales_totalSize_upper
import Theorems.Thm_ThreeSum_Scales_totalSize_lower

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {m : ℕ} (hm : 0 < microSize m) :
    (m : ℝ) / 5 - 20 * microSize m < totalSize m ∧
      (totalSize m : ℝ) ≤ (m : ℝ) / 5 := by
  have hu : (5 : ℝ) * totalSize m ≤ (m : ℝ) := by
    exact_mod_cast totalSize_upper m
  have hl : (m : ℝ) < 5 * totalSize m + 100 * microSize m := by
    exact_mod_cast totalSize_lower hm
  constructor <;> linarith
end ThreeSum.Scales
