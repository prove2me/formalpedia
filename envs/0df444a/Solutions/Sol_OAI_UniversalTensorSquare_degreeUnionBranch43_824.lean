-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_824
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:21:55.585367+00:00
-- url     : https://prove2.me/submissions/2734c14c-d7f2-43ce-a1c1-1a977bb04de8

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

lemma degreeUnionBranch43_824_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 30 13 degreeUnionState43_824 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_824_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_824_oai
