-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_66
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:29:51.088609+00:00
-- url     : https://prove2.me/submissions/e05b54f0-b618-481c-8ed6-9fda77ec0d8c

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

lemma degreeUnionBranch43_66_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 15 14 degreeUnionState43_66 [14,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_66_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_66_oai
