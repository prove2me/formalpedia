-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_677
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:31:40.252034+00:00
-- url     : https://prove2.me/submissions/b6a52d64-3d2a-4b45-9453-de400f26efd0

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

lemma degreeUnionBranch43_677_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 7 36 degreeUnionState43_677 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_677_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_677_oai
