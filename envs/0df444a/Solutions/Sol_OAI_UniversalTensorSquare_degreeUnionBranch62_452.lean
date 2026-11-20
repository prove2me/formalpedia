-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_452
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:16:28.424592+00:00
-- url     : https://prove2.me/submissions/97e5c943-1704-43da-b7aa-1471de276aa4

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

lemma degreeUnionBranch62_452_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 4 degreeUnionState62_452 [4,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_452_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_452_oai
