-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_808
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:11:26.762603+00:00
-- url     : https://prove2.me/submissions/3f4a0fe4-4ba8-4c1f-ae18-404e32ba8411

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

lemma degreeUnionBranch43_808_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 5 38 degreeUnionState43_808 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_808_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_808_oai
