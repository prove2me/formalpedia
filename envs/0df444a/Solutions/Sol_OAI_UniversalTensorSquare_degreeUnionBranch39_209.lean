-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_209
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:55:23.451401+00:00
-- url     : https://prove2.me/submissions/0e124441-0c7b-4ab6-9ac8-ba2e9f9eb069

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

lemma degreeUnionBranch39_209_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 16 23 degreeUnionState39_209 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_209_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_209_oai
