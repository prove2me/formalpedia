-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_826
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:16:37.123978+00:00
-- url     : https://prove2.me/submissions/f23a2943-c5a6-4800-b7fa-8f9b68deb948

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

lemma degreeUnionBranch43_826_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 28 15 degreeUnionState43_826 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_826_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_826_oai
