-- Prove2me | solution 1 for ThreeSum.Scales.microSize_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:58:04.698597+00:00
-- url     : https://prove2.me/submissions/ad74dfb8-ec35-4561-af12-8a376c56eff2

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
import Theorems.Thm_ThreeSum_Scales_microSize_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_microSize_square_ratio_tendsto_zero

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun m : ℕ => (microSize m : ℝ) / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ microSize_square_ratio_tendsto_zero
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hmr : (1 : ℝ) ≤ microSize m := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg m)
end ThreeSum.Scales
