-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_725
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:41:03.08074+00:00
-- url     : https://prove2.me/submissions/97ef6d7e-927c-4bd3-9293-41d92e539034

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

lemma degreeUnionBranch43_725_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 7 36 degreeUnionState43_725 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_725_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_725_oai
