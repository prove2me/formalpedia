-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_792
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:10:56.133632+00:00
-- url     : https://prove2.me/submissions/759b29ee-9587-4fb9-886d-f5aa7ba8acd8

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

lemma degreeUnionBranch43_792_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 21 22 degreeUnionState43_792 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_792_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_792_oai
