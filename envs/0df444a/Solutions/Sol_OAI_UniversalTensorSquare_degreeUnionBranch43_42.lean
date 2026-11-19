-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_42
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:43.363206+00:00
-- url     : https://prove2.me/submissions/6d1ac84b-95c9-48e6-ab77-6d29857a6b65

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

lemma degreeUnionBranch43_42_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 22 9 degreeUnionState43_42 [9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_42_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_42_oai
