-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_825
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:22:01.549111+00:00
-- url     : https://prove2.me/submissions/07401505-3881-4cb5-acd7-c035b1f78d24

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

lemma degreeUnionBranch43_825_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 29 14 degreeUnionState43_825 [14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_825_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_825_oai
