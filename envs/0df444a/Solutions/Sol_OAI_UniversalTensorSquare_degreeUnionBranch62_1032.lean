-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1032
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:10:02.651449+00:00
-- url     : https://prove2.me/submissions/f14dfe99-a737-499d-9b56-af8b4f912431

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

lemma degreeUnionBranch62_1032_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 3 degreeUnionState62_1032 [3,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1032_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1032_oai
