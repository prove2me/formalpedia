-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_297
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:04:48.023721+00:00
-- url     : https://prove2.me/submissions/33ce2264-f2cd-4aa6-9d25-f8b51eed9dd3

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

lemma degreeUnionBranch39_297_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 11 28 degreeUnionState39_297 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_297_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_297_oai
