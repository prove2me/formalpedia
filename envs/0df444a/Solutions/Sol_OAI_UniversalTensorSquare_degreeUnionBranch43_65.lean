-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_65
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:27:33.804268+00:00
-- url     : https://prove2.me/submissions/113390ac-72f9-4e0f-9431-83427ff2db7c

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

lemma degreeUnionBranch43_65_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 16 13 degreeUnionState43_65 [13,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_65_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_65_oai
