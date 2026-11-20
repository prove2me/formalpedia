-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:11:29.934593+00:00
-- url     : https://prove2.me/submissions/a554a86c-b24a-4a83-80fc-932ecc368cdf

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

lemma degreeUnionBranch64_8_oai : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 8 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch64_8_oai := @OAI.UniversalTensorSquare.degreeUnionBranch64_8_oai
