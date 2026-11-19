-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_331
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:44:42.105966+00:00
-- url     : https://prove2.me/submissions/21f33ffe-9edd-4205-b5ca-a2ed38e8908b

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

lemma degreeUnionBranch43_331_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 23 degreeUnionState43_331 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_331_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_331_oai
