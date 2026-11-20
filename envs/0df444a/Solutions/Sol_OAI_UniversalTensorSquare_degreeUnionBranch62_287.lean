-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_287
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:39:49.603188+00:00
-- url     : https://prove2.me/submissions/095d87a1-d1fe-47e6-8afc-902012a140cc

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

lemma degreeUnionBranch62_287_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 6 degreeUnionState62_287 [6,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_287_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_287_oai
