-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_half_Hpi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:59.162662+00:00
-- url     : https://prove2.me/submissions/044cceb3-3866-442a-aa1a-c3b8350db253

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_bits_lt_quarter

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000 * m).choose (292746547000 * m) : ℕ) : ℝ) /
      ((30000000000000 * m : ℕ) * Real.log 2) < Hpi / 2 := by
  linarith [projection_fiber_bits_lt_quarter hm, Hpi_bounds.1]
end ThreeSum.WeightedGlobalParameters
