-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_263
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:30:59.545174+00:00
-- url     : https://prove2.me/submissions/5a649842-7685-4ecb-81ec-65f06a6a0e9b

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

lemma degreeUnionBranch62_263_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 37 5 degreeUnionState62_263 [5,7,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_263_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_263_oai
