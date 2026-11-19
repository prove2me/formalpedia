-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_833
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:26:49.384757+00:00
-- url     : https://prove2.me/submissions/697f9ad0-ba48-4e62-8f4e-4d00949a8b52

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

lemma degreeUnionBranch43_833_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 21 22 degreeUnionState43_833 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_833_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_833_oai
