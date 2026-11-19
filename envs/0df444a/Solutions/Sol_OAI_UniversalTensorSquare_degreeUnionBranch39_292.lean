-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_292
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:01:42.559435+00:00
-- url     : https://prove2.me/submissions/6ed0ca6c-9ac4-4ed8-8546-756a8313fa9f

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

lemma degreeUnionBranch39_292_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 16 23 degreeUnionState39_292 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_292_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_292_oai
