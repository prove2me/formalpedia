-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_278
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:40:36.782868+00:00
-- url     : https://prove2.me/submissions/58409f76-b3ab-4947-b7fb-ea07faccb928

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

lemma degreeUnionBranch43_278_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 11 16 degreeUnionState43_278 [16,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_278_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_278_oai
