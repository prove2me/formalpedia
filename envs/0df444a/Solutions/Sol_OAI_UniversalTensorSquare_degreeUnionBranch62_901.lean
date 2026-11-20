-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_901
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:20:06.471756+00:00
-- url     : https://prove2.me/submissions/b8f36719-a363-4ad5-aa83-a9022092a085

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

lemma degreeUnionBranch62_901_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 10 degreeUnionState62_901 [10,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_901_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_901_oai
