-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:40:33.601931+00:00
-- url     : https://prove2.me/submissions/c50aa033-5f0c-430a-bdf8-4fe8665ece77

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

lemma degreeUnionBranch35_46_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 6 29 degreeUnionState35_46 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_46_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_46_oai
