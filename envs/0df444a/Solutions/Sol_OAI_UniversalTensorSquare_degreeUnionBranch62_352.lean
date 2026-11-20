-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_352
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:21:44.740993+00:00
-- url     : https://prove2.me/submissions/3bd7099f-ca71-4e15-950b-00701ee2ab99

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

lemma degreeUnionBranch62_352_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 4 degreeUnionState62_352 [4,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_352_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_352_oai
