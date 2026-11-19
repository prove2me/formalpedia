-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_214
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:55:52.664125+00:00
-- url     : https://prove2.me/submissions/aafcea2e-c40a-40f7-b7b8-a395243b4abb

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_214_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 11 28 degreeUnionState39_214 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_214_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_214_oai
