-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_178
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:20:13.756708+00:00
-- url     : https://prove2.me/submissions/83f9b153-a468-457d-8a44-cba9f8272d9d

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

lemma degreeUnionBranch43_178_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 4 39 degreeUnionState43_178 [39] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_178_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_178_oai
