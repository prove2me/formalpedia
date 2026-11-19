-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_224
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:59:36.251875+00:00
-- url     : https://prove2.me/submissions/e0d65d3e-c6de-4b5c-b099-cd27da44e175

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

lemma degreeUnionBranch39_224_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 1 38 degreeUnionState39_224 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_224_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_224_oai
