-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_213
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:55:46.794534+00:00
-- url     : https://prove2.me/submissions/d862d6cf-184f-4ab5-89d0-f0bbb867341c

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

lemma degreeUnionBranch39_213_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 12 27 degreeUnionState39_213 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_213_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_213_oai
