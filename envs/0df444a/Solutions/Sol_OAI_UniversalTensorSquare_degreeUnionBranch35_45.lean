-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_45
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:40:27.634454+00:00
-- url     : https://prove2.me/submissions/24947d74-a404-452c-b4e0-e732e53bd2d0

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

lemma degreeUnionBranch35_45_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 7 28 degreeUnionState35_45 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_45_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_45_oai
