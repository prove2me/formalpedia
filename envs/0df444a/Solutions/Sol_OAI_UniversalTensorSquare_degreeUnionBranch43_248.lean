-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_248
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:38.19334+00:00
-- url     : https://prove2.me/submissions/5d3e7939-0395-496f-a356-c1eb2428da0f

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

lemma degreeUnionBranch43_248_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 11 degreeUnionState43_248 [11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_248_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_248_oai
