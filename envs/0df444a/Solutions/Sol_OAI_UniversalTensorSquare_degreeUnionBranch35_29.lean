-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:36:14.318261+00:00
-- url     : https://prove2.me/submissions/c6e1153e-4bb0-4db6-89ba-a836f282be03

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

lemma degreeUnionBranch35_29_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 23 12 degreeUnionState35_29 [12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_29_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_29_oai
