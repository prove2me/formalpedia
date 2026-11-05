-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.gibbs_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:17.526554+00:00
-- url     : https://prove2.me/submissions/0b1f6d37-2d6a-4c7f-b02d-26625d95598d

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
theorem _root_.solution : 0<y ∧ y<1 ∧ 0<z ∧ z<1 := by
  norm_num [y,z,WeightedCacheParameters_e1ae71d.yRoot,WeightedCacheParameters_e1ae71d.zRoot]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
