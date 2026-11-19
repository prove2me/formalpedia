-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_275
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:40:19.141635+00:00
-- url     : https://prove2.me/submissions/10ab5cb6-64ac-4d6a-8fb3-ba301b404c2a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_275_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 14 13 degreeUnionState43_275 [13,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_275_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_275_oai
