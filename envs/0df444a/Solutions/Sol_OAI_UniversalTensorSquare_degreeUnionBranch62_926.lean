-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_926
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:37:04.6963+00:00
-- url     : https://prove2.me/submissions/17b90cc3-a6e1-4b33-a535-36f091ca3505

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_926_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 7 degreeUnionState62_926 [7,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_926_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_926_oai
