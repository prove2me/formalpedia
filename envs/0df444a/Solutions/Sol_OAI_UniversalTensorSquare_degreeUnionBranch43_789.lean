-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_789
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:05:55.897327+00:00
-- url     : https://prove2.me/submissions/0b1c8a76-b38b-4538-b139-5a3f499564a9

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

lemma degreeUnionBranch43_789_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 24 19 degreeUnionState43_789 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_789_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_789_oai
