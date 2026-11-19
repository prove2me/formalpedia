-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_742
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:45:21.865749+00:00
-- url     : https://prove2.me/submissions/51fc3345-1840-44ec-a0cb-3396bf61b016

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

lemma degreeUnionBranch43_742_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 30 13 degreeUnionState43_742 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_742_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_742_oai
