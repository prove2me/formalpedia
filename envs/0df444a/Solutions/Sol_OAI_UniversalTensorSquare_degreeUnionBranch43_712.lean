-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_712
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:39:38.277744+00:00
-- url     : https://prove2.me/submissions/209cf290-6b37-4cd4-b976-4017f1802e6a

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

lemma degreeUnionBranch43_712_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 20 23 degreeUnionState43_712 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_712_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_712_oai
