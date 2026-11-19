-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_208
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:55:17.676646+00:00
-- url     : https://prove2.me/submissions/366e8fb8-c9d7-4034-99e2-9e4e37994f21

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

lemma degreeUnionBranch39_208_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 17 22 degreeUnionState39_208 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_208_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_208_oai
