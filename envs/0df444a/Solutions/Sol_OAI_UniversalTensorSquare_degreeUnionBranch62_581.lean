-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_581
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:59:56.439096+00:00
-- url     : https://prove2.me/submissions/47763328-ce48-4042-ba88-3d7ffe561a1c

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

lemma degreeUnionBranch62_581_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 6 degreeUnionState62_581 [6,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_581_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_581_oai
