-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_417
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:25.525976+00:00
-- url     : https://prove2.me/submissions/8366bc2e-ddcb-43bb-a599-24c440088c3f

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

lemma degreeUnionBranch43_417_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 21 9 degreeUnionState43_417 [9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_417_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_417_oai
