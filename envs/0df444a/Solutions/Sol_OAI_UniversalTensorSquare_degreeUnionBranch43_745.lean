-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_745
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:45:39.717854+00:00
-- url     : https://prove2.me/submissions/b0d75b96-8c26-48a2-a96d-ea368582b8ca

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

lemma degreeUnionBranch43_745_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 27 16 degreeUnionState43_745 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_745_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_745_oai
