-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_855
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:56:10.151051+00:00
-- url     : https://prove2.me/submissions/9356e9ce-75b6-4164-91bd-80447fcceb47

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

lemma degreeUnionBranch62_855_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 4 degreeUnionState62_855 [4,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_855_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_855_oai
