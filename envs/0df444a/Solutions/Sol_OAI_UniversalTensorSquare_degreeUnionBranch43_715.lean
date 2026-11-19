-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_715
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:39:56.574142+00:00
-- url     : https://prove2.me/submissions/ab48a50c-bc05-4c9f-856c-58d36e609aad

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

lemma degreeUnionBranch43_715_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 17 26 degreeUnionState43_715 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_715_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_715_oai
