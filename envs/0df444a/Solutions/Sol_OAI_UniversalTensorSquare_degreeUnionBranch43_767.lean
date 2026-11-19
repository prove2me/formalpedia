-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_767
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:50:59.483073+00:00
-- url     : https://prove2.me/submissions/6367c0e9-5db8-41c5-9882-714a5a555570

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

lemma degreeUnionBranch43_767_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 5 38 degreeUnionState43_767 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_767_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_767_oai
