-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_73
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:41:32.968208+00:00
-- url     : https://prove2.me/submissions/3c4c47b7-d3e6-4bf0-abc0-bdb93019c749

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

lemma degreeUnionBranch43_73_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 19 9 degreeUnionState43_73 [9,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_73_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_73_oai
