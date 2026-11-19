-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_120
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:35.068531+00:00
-- url     : https://prove2.me/submissions/a4213c65-8461-44a9-b60c-2692f887efe4

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

lemma degreeUnionBranch39_120_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 1 38 degreeUnionState39_120 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_120_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_120_oai
