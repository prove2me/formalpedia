-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:11:23.003456+00:00
-- url     : https://prove2.me/submissions/e95c2f38-81f8-4bd7-909c-45c703bf0b5c

import Mathlib
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 64. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch64_3_oai : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 3 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch64_3_oai := @OAI.UniversalTensorSquare.degreeUnionBranch64_3_oai
