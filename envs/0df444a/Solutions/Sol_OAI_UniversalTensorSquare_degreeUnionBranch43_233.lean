-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_233
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:00.608595+00:00
-- url     : https://prove2.me/submissions/7b7b7cd4-ac85-436b-8a50-af1e7baa4cf6

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

lemma degreeUnionBranch43_233_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 7 degreeUnionState43_233 [7,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_233_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_233_oai
