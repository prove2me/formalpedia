-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_862
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:22:19.8413+00:00
-- url     : https://prove2.me/submissions/f42ce7c4-39d3-4ae7-8ce9-442da26f1253

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

lemma degreeUnionBranch43_862_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 33 10 degreeUnionState43_862 [10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_862_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_862_oai
