-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_437
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:16.877172+00:00
-- url     : https://prove2.me/submissions/8c3d948c-dda4-4dfe-87c0-820665b60d55

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

lemma degreeUnionBranch43_437_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 6 degreeUnionState43_437 [6,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_437_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_437_oai
