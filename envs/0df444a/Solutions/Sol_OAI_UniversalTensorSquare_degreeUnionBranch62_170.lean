-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_170
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:39:23.860683+00:00
-- url     : https://prove2.me/submissions/5056fe44-df2a-4d08-a9ec-0a0a263576ef

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_170_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 7 degreeUnionState62_170 [7,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_170_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_170_oai
