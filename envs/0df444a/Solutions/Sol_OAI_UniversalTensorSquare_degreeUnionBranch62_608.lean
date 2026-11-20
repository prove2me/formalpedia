-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_608
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:11:07.490329+00:00
-- url     : https://prove2.me/submissions/b6d6b4c1-575d-4ba4-af35-d6dd9e9707ed

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

lemma degreeUnionBranch62_608_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 4 degreeUnionState62_608 [4,8,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_608_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_608_oai
