-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_354
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:21:57.56186+00:00
-- url     : https://prove2.me/submissions/3fec25ee-2feb-48fc-906b-bbc6e49a492d

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

lemma degreeUnionBranch62_354_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 6 degreeUnionState62_354 [6,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_354_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_354_oai
