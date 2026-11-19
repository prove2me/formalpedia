-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_402
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:50.170003+00:00
-- url     : https://prove2.me/submissions/b6abc870-9a5e-49e2-912c-36c5ba0b294d

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

lemma degreeUnionBranch43_402_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 27 4 degreeUnionState43_402 [4,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_402_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_402_oai
