-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_lt_half_Hpi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:21.321609+00:00
-- url     : https://prove2.me/submissions/9d7fa99d-610d-46ba-8f48-993feb1df4ec

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Hpi_bounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_projection_fiber_entropy_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    Real.binEntropy alpha2 / Real.log 2 < Hpi / 2 := by
  linarith [projection_fiber_entropy_bound, Hpi_bounds.1]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
