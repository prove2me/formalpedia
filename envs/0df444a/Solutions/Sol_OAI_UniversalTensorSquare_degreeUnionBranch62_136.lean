-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_136
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:29:58.975612+00:00
-- url     : https://prove2.me/submissions/5e3f4bb7-9c8a-484b-8f7b-fd69d14058c1

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

lemma degreeUnionBranch62_136_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 37 6 degreeUnionState62_136 [6,7,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_136_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_136_oai
