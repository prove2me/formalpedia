-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_332
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:08:22.426212+00:00
-- url     : https://prove2.me/submissions/1d506e3b-e126-4d97-93ac-90f91036e884

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

lemma degreeUnionBranch62_332_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 7 degreeUnionState62_332 [7,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_332_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_332_oai
