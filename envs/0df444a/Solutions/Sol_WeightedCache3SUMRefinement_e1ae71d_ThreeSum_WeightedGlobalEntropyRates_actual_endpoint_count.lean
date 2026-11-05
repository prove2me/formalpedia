-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.actual_endpoint_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:28:02.771349+00:00
-- url     : https://prove2.me/submissions/9ed0c702-5a2f-469c-b8b4-3b60e7963d9c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_fixedAlpha_total
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_choose


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution (m : ℕ) :
    endpointSize m=typeCount 30000000000000000 2672696394564960 292929977780940 m := by
  unfold endpointSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedAlpha m) (fixedAlpha_total m)]
  change (30000000000000000*m).choose (292929977780940*m)*(30000000000000000*m-292929977780940*m).choose (2672696394564960*m)=
    (30000000000000000*m).choose (292929977780940*m)*((30000000000000000-292929977780940)*m).choose (2672696394564960*m)
  rw [← Nat.sub_mul]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
