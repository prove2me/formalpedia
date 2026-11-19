-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_870
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:31:54.990841+00:00
-- url     : https://prove2.me/submissions/cdf411ed-502d-45aa-b241-aadca5d5f6c0

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

lemma degreeUnionBranch43_870_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 25 18 degreeUnionState43_870 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_870_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_870_oai
