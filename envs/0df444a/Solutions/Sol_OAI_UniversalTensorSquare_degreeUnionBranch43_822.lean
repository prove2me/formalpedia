-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_822
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:21:49.256205+00:00
-- url     : https://prove2.me/submissions/ee7fcda9-12f7-4b89-b7c5-23f3f4445722

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

lemma degreeUnionBranch43_822_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 32 11 degreeUnionState43_822 [11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_822_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_822_oai
