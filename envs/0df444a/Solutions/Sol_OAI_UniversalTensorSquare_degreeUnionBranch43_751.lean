-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_751
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:46:04.179229+00:00
-- url     : https://prove2.me/submissions/c3bcf43b-6b00-4bbf-ae93-976a262f7a6d

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

lemma degreeUnionBranch43_751_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 21 22 degreeUnionState43_751 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_751_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_751_oai
