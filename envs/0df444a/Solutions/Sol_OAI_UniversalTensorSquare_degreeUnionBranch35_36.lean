-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:36:55.07848+00:00
-- url     : https://prove2.me/submissions/28ea8bc0-2f74-415c-87b5-bb112f9f12f7

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

lemma degreeUnionBranch35_36_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 16 19 degreeUnionState35_36 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_36_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_36_oai
