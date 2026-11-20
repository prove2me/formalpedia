-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_761
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:06:51.891008+00:00
-- url     : https://prove2.me/submissions/1252f74e-f459-4122-b9cd-d75ef09dba9c

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

lemma degreeUnionBranch62_761_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 4 degreeUnionState62_761 [4,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_761_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_761_oai
