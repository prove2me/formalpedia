-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:01:18.811239+00:00
-- url     : https://prove2.me/submissions/bf725898-c84c-4649-be21-41c014566f48

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

lemma degreeUnionBranch64_10_oai : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 10 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch64_10_oai := @OAI.UniversalTensorSquare.degreeUnionBranch64_10_oai
