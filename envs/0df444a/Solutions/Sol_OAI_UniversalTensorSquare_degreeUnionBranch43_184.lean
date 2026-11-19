-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_184
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:20:49.108212+00:00
-- url     : https://prove2.me/submissions/27c0c3ed-0685-4827-a8b0-94acab078e2e

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

lemma degreeUnionBranch43_184_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 37 6 degreeUnionState43_184 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_184_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_184_oai
