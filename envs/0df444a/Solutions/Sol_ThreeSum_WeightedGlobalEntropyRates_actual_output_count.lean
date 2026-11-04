-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.actual_output_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:59.276218+00:00
-- url     : https://prove2.me/submissions/2acc0607-9aad-4bc6-b898-0154434dad13

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_choose
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution (m : ℕ) :
    outputSize m=typeCount 30000000000000 4760008248000 878239641000 m := by
  unfold outputSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedPi m) (fixedPi_total m)]
  change (30000000000000*m).choose (878239641000*m)*(30000000000000*m-878239641000*m).choose (4760008248000*m)=
    (30000000000000*m).choose (878239641000*m)*((30000000000000-878239641000)*m).choose (4760008248000*m)
  rw [← Nat.sub_mul]
end ThreeSum.WeightedGlobalEntropyRates
