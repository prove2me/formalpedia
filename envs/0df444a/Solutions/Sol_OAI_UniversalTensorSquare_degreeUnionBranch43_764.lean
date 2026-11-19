-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_764
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:50:47.300832+00:00
-- url     : https://prove2.me/submissions/20b0c95d-d4b1-4b71-ae7c-a01905456f5d

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

lemma degreeUnionBranch43_764_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 8 35 degreeUnionState43_764 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_764_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_764_oai
