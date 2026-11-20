-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_444
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:16:02.277109+00:00
-- url     : https://prove2.me/submissions/d47af9a9-e149-4eca-bc40-a57c8cca8eb3

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

lemma degreeUnionBranch62_444_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 5 degreeUnionState62_444 [5,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_444_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_444_oai
