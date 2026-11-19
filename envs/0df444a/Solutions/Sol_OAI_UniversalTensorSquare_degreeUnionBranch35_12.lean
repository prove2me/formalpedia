-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:35:38.980999+00:00
-- url     : https://prove2.me/submissions/e2f3d741-78a5-4b21-8d70-e043e60ce04f

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

lemma degreeUnionBranch35_12_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 27 8 degreeUnionState35_12 [8] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_12_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_12_oai
