-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_282
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:35:28.798711+00:00
-- url     : https://prove2.me/submissions/6d2e7202-1482-406f-9f08-24c422e4f337

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

lemma degreeUnionBranch62_282_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 7 degreeUnionState62_282 [7,8,8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_282_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_282_oai
