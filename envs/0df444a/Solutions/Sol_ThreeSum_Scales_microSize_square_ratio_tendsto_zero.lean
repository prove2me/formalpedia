-- Prove2me | solution 1 for ThreeSum.Scales.microSize_square_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:25.24248+00:00
-- url     : https://prove2.me/submissions/90e8a425-faed-4d23-9a9d-1cf95a523000

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
import Theorems.Thm_ThreeSum_Scales_microSize_inv_tendsto_zero
import Theorems.Thm_ThreeSum_Scales_microSize_square_ratio_bound

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ microSize_inv_tendsto_zero
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    exact microSize_square_ratio_bound (by omega)
end ThreeSum.Scales
