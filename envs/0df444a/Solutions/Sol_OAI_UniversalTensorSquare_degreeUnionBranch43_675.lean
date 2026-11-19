-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_675
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:31:27.906813+00:00
-- url     : https://prove2.me/submissions/10204f41-5b50-47bf-b87a-6f3199c2ea6d

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

lemma degreeUnionBranch43_675_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 9 34 degreeUnionState43_675 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_675_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_675_oai
