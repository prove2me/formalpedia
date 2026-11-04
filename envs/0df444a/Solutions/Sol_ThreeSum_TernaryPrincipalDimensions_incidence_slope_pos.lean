-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.incidence_slope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:47.837443+00:00
-- url     : https://prove2.me/submissions/fb928d3c-1097-4c37-9e49-670b2697a0c7

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryEntropyRates_denominator_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < incidenceSlope m := by
  have hs' : Real.log (prime m : ℝ)/((fixedLength m : ℝ)*Real.log 2) <
    Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) := hs
  exact sub_pos.mpr ((div_lt_div_iff_of_pos_right (denominator_pos hm)).mp hs')
end ThreeSum.TernaryPrincipalDimensions
