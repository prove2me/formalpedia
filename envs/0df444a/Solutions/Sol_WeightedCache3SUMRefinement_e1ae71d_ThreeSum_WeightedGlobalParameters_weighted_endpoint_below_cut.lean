-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.weighted_endpoint_below_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:15.659087+00:00
-- url     : https://prove2.me/submissions/c65c28c8-c784-4fe1-88d4-e832e2923246

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 2740*(alpha1+2*alpha2)<2*cutSlope := by
  norm_num [alpha1,alpha2,cutSlope]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
