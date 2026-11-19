-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:32.426473+00:00
-- url     : https://prove2.me/submissions/7fa94e50-8761-4d12-b911-0320e949007f

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

lemma degreeUnionBranch43_247_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 10 degreeUnionState43_247 [10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_247_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_247_oai
