-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_258
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:23:30.795471+00:00
-- url     : https://prove2.me/submissions/438f69f9-94be-4beb-bac6-70ad96cc2b42

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

lemma degreeUnionBranch62_258_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 12 degreeUnionState62_258 [12,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_258_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_258_oai
