-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_41
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:02:37.642214+00:00
-- url     : https://prove2.me/submissions/17e30af1-29de-463f-8b22-3a94a1c88b9b

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

lemma degreeUnionBranch43_41_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 23 8 degreeUnionState43_41 [8,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_41_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_41_oai
