-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.incidence_slope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:54:20.711211+00:00
-- url     : https://prove2.me/submissions/86a1a6ec-f8bf-4069-8156-4ba25dff57e1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_denominator_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < incidenceSlope m := by
  have hs' : Real.log (prime m : ℝ)/((fixedLength m : ℝ)*Real.log 2) <
    Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) := hs
  exact sub_pos.mpr ((div_lt_div_iff_of_pos_right (denominator_pos hm)).mp hs')
end ThreeSum.WeightedGlobalPrincipalDimensions
