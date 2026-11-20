-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_358
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:26:54.839179+00:00
-- url     : https://prove2.me/submissions/3b7b2970-7093-4c05-8242-6e1277df4f4f

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

lemma degreeUnionBranch62_358_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 10 degreeUnionState62_358 [10,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_358_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_358_oai
