-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_114
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:47:08.030807+00:00
-- url     : https://prove2.me/submissions/29c6d1b2-a827-4ba5-aed6-a7ed939814b3

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

lemma degreeUnionBranch39_114_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 7 32 degreeUnionState39_114 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_114_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_114_oai
