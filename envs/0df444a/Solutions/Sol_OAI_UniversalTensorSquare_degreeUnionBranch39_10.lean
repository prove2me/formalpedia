-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:32.058299+00:00
-- url     : https://prove2.me/submissions/2c5cbdf0-b466-4c2a-ab3e-7604da673fcb

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

lemma degreeUnionBranch39_10_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 33 6 degreeUnionState39_10 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_10_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_10_oai
