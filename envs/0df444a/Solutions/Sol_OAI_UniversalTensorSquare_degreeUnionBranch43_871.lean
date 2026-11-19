-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_871
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:32:01.173442+00:00
-- url     : https://prove2.me/submissions/80d97e4f-3699-487a-81e9-ec8abc94c400

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

lemma degreeUnionBranch43_871_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 24 19 degreeUnionState43_871 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_871_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_871_oai
