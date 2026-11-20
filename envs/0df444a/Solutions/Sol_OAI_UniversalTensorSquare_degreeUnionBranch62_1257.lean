-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1257
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:51:02.559498+00:00
-- url     : https://prove2.me/submissions/d52f9188-24cc-4485-b4b5-0d4e729bf2e8

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

lemma degreeUnionBranch62_1257_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 6 degreeUnionState62_1257 [6,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1257_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1257_oai
