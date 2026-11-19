-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_291
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:01:36.561995+00:00
-- url     : https://prove2.me/submissions/aa1e0405-98b1-4e56-a398-41412ff00736

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

lemma degreeUnionBranch39_291_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 17 22 degreeUnionState39_291 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_291_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_291_oai
