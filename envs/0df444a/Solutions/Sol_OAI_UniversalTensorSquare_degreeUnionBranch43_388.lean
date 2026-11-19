-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_388
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:54:33.291654+00:00
-- url     : https://prove2.me/submissions/a44204d5-efeb-4c15-ad0d-9555460c26b3

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

lemma degreeUnionBranch43_388_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 7 degreeUnionState43_388 [7,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_388_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_388_oai
