-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:47:10.025426+00:00
-- url     : https://prove2.me/submissions/ecfcb3ec-7002-4537-b6bb-ae4c101f6bd3

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_77_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 36 10 degreeUnionState58_77 [10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_77_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_77_oai
