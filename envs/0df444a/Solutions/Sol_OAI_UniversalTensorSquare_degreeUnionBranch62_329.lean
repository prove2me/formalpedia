-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_329
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:07:56.356218+00:00
-- url     : https://prove2.me/submissions/6ba2507e-2e75-45c2-8507-0b83f5a6bdd6

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

lemma degreeUnionBranch62_329_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 4 degreeUnionState62_329 [4,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_329_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_329_oai
