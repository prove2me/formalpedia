-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_294
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:01:54.384044+00:00
-- url     : https://prove2.me/submissions/4568e5cf-8e77-423c-a4be-e0757ed717c8

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

lemma degreeUnionBranch39_294_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 14 25 degreeUnionState39_294 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_294_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_294_oai
