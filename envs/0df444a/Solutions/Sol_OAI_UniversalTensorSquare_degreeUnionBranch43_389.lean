-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_389
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:54:39.204147+00:00
-- url     : https://prove2.me/submissions/db865de5-0f27-4877-93e3-7bc236196c21

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

lemma degreeUnionBranch43_389_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 8 degreeUnionState43_389 [8,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_389_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_389_oai
