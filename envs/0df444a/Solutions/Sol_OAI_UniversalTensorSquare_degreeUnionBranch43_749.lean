-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_749
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:50:12.070632+00:00
-- url     : https://prove2.me/submissions/60d2b22c-e4d1-4cfb-a7c2-d924018d5321

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

lemma degreeUnionBranch43_749_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 23 20 degreeUnionState43_749 [20] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_749_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_749_oai
