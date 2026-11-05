-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:15:10.634084+00:00
-- url     : https://prove2.me/submissions/f47f4a09-54bf-44f3-8486-5bf75405603d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
theorem _root_.solution : program.length=17 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
