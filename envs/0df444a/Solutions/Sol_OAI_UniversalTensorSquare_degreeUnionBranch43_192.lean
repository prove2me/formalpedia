-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_192
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:23:50.125649+00:00
-- url     : https://prove2.me/submissions/2521976b-cefd-4aa5-a2e4-1e4cc1ff96b5

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

lemma degreeUnionBranch43_192_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 29 5 degreeUnionState43_192 [5,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_192_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_192_oai
