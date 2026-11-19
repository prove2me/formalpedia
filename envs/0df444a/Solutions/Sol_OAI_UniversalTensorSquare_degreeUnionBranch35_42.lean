-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_42
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:37:29.904572+00:00
-- url     : https://prove2.me/submissions/217f3713-4702-4ff5-b8d3-ac1b7f034c1d

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_42_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 10 25 degreeUnionState35_42 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_42_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_42_oai
