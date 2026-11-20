-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1164
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:13:16.287192+00:00
-- url     : https://prove2.me/submissions/997b6853-2eae-4b5e-996f-19517ceb003f

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

lemma degreeUnionBranch62_1164_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 3 degreeUnionState62_1164 [3,8,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1164_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1164_oai
