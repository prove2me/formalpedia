-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_105
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:46:08.173592+00:00
-- url     : https://prove2.me/submissions/2218d05c-8a18-47fa-9f27-f3ce548bbee6

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

lemma degreeUnionBranch39_105_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 16 23 degreeUnionState39_105 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_105_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_105_oai
