-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_160
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:15:26.205207+00:00
-- url     : https://prove2.me/submissions/09e68011-9d34-4686-a830-e8af1f1145ec

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

lemma degreeUnionBranch43_160_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 21 degreeUnionState43_160 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_160_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_160_oai
