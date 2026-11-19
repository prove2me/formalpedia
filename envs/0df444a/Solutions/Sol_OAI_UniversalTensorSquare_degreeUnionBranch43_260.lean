-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_260
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:39:20.254842+00:00
-- url     : https://prove2.me/submissions/b14a52ae-96b1-41cd-bd68-f5416d92b1d0

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

lemma degreeUnionBranch43_260_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 11 degreeUnionState43_260 [11,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_260_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_260_oai
