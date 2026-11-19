-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_72
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:40:26.807833+00:00
-- url     : https://prove2.me/submissions/42ca8ef4-1e9a-4817-88b4-f24184aa25f4

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

lemma degreeUnionBranch43_72_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 20 8 degreeUnionState43_72 [8,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_72_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_72_oai
