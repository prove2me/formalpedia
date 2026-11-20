-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:07:13.593908+00:00
-- url     : https://prove2.me/submissions/29de8c7b-d279-42ef-a30c-26780b8f4ba1

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

lemma degreeUnionBranch64_6_oai : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 6 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch64_6_oai := @OAI.UniversalTensorSquare.degreeUnionBranch64_6_oai
