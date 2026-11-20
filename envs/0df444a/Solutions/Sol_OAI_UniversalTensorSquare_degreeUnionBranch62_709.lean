-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_709
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:54:33.774359+00:00
-- url     : https://prove2.me/submissions/5deeb7ee-ed8c-445c-83f1-1f8b81c42345

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

lemma degreeUnionBranch62_709_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 43 6 degreeUnionState62_709 [6,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_709_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_709_oai
