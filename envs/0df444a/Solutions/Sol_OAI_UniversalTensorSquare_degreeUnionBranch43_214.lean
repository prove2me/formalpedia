-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_214
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:28:56.769968+00:00
-- url     : https://prove2.me/submissions/594230a8-1a62-4954-bd42-73a39ea4d63f

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

lemma degreeUnionBranch43_214_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 7 degreeUnionState43_214 [7,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_214_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_214_oai
