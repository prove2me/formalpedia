-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_783
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:00:49.618365+00:00
-- url     : https://prove2.me/submissions/ad6548e0-8bb9-4b17-8895-859543e59355

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

lemma degreeUnionBranch43_783_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 30 13 degreeUnionState43_783 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_783_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_783_oai
