-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_399
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:20.150147+00:00
-- url     : https://prove2.me/submissions/d24956d7-0b11-47c1-bcbf-c4b6c886d730

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

lemma degreeUnionBranch43_399_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 10 degreeUnionState43_399 [10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_399_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_399_oai
