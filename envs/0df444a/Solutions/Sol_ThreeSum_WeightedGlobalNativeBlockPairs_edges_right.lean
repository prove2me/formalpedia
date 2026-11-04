-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeBlockPairs.edges_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:40:48.92273+00:00
-- url     : https://prove2.me/submissions/c0563341-73b1-4a48-b84c-7f1e3b650341

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
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : right (edges a b q h i)=(b i).val := rfl
end ThreeSum.WeightedGlobalNativeBlockPairs
