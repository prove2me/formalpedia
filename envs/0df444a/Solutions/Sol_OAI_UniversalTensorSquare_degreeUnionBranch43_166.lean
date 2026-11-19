-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_166
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:19:02.388726+00:00
-- url     : https://prove2.me/submissions/4f38e138-ae58-4a02-99ca-fa2f563495dc

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

lemma degreeUnionBranch43_166_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 16 27 degreeUnionState43_166 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_166_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_166_oai
