-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_227
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:30:20.916695+00:00
-- url     : https://prove2.me/submissions/58cceb8e-326b-42b7-9f7b-742bb206a252

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_227_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 11 degreeUnionState43_227 [11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_227_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_227_oai
