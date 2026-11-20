-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_300
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:48:51.795179+00:00
-- url     : https://prove2.me/submissions/07e3b949-3ba8-4715-889a-9321da511c50

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

lemma degreeUnionBranch62_300_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 4 degreeUnionState62_300 [4,9,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_300_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_300_oai
