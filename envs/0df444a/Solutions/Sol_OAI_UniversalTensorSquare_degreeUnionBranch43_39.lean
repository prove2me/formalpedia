-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:54:45.675638+00:00
-- url     : https://prove2.me/submissions/72c56b98-5e10-41a2-b1ac-39ba77ea8c40

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

lemma degreeUnionBranch43_39_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 25 6 degreeUnionState43_39 [6,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_39_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_39_oai
