-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.query_slope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:53.004965+00:00
-- url     : https://prove2.me/submissions/7c753350-2698-42d9-b760-a4b235045a56

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_incidence_slope_pos
import Theorems.Thm_ThreeSum_TernaryEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_TernaryParameters_analytic_admissibility


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < querySlope m := by
  unfold querySlope
  exact add_pos (incidence_slope_pos hm hs)
    (mul_pos (denominator_pos hm) analytic_admissibility.2.1)
end ThreeSum.TernaryPrincipalDimensions
