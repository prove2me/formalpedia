-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_809
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:11:32.71836+00:00
-- url     : https://prove2.me/submissions/55deea92-4c5a-4c3e-a3ee-f2a3be88e142

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

lemma degreeUnionBranch43_809_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 4 39 degreeUnionState43_809 [39] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_809_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_809_oai
