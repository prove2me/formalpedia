-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:43:54.485587+00:00
-- url     : https://prove2.me/submissions/76fb5e32-6c35-4cdd-9cac-89ea1ce8cb0c

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

lemma degreeUnionBranch43_30_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 27 5 degreeUnionState43_30 [5,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_30_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_30_oai
