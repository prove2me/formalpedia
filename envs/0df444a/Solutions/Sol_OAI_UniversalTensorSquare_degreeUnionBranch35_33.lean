-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:36:37.325276+00:00
-- url     : https://prove2.me/submissions/0222ad10-0bae-47c4-98e6-9686414538c2

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

lemma degreeUnionBranch35_33_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 19 16 degreeUnionState35_33 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_33_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_33_oai
