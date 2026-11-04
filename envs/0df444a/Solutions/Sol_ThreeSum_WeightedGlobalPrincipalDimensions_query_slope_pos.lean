-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.query_slope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:02:25.270308+00:00
-- url     : https://prove2.me/submissions/90fa57db-73cf-43c7-83d3-81c0b99bb04b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_slope_pos
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_analytic_admissibility


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < querySlope m := by
  unfold querySlope
  exact add_pos (incidence_slope_pos hm hs)
    (mul_pos (denominator_pos hm) analytic_admissibility.2.1)
end ThreeSum.WeightedGlobalPrincipalDimensions
