-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_43
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:40:16.084056+00:00
-- url     : https://prove2.me/submissions/037f70ea-55c6-40a3-b0ba-e32a1b80fbe9

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

lemma degreeUnionBranch35_43_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 9 26 degreeUnionState35_43 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_43_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_43_oai
