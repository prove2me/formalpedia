-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.actual_output_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:26:32.498788+00:00
-- url     : https://prove2.me/submissions/34729b6d-f4f0-43b9-93ba-a0c59b24751b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_choose
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


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
    outputSize m=typeCount 30000000000000000 4759532833568040 878789933342820 m := by
  unfold outputSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedPi m) (fixedPi_total m)]
  change (30000000000000000*m).choose (878789933342820*m)*(30000000000000000*m-878789933342820*m).choose (4759532833568040*m)=
    (30000000000000000*m).choose (878789933342820*m)*((30000000000000000-878789933342820)*m).choose (4759532833568040*m)
  rw [← Nat.sub_mul]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
