-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:29:29.18432+00:00
-- url     : https://prove2.me/submissions/c780726d-842b-4a86-80c8-3682072b6c5d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeBlockPairs
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
variable {r L F : ℕ} {α π : DigitType}
namespace ThreeSum.WeightedGlobalNativeBlockPairs
theorem _root_.solution (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : left (edges a b q h i)=(a i).val := rfl
end ThreeSum.WeightedGlobalNativeBlockPairs
