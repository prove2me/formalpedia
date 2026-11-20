-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_786
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:13:08.862336+00:00
-- url     : https://prove2.me/submissions/e95d4b1d-10aa-4845-ac5d-0eeceacceeb0

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

lemma degreeUnionBranch62_786_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 3 degreeUnionState62_786 [3,8,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_786_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_786_oai
