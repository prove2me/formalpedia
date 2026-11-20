-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_793
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:18:25.686283+00:00
-- url     : https://prove2.me/submissions/2a633dda-b4f9-4f60-8c68-e1483b7b972a

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

lemma degreeUnionBranch62_793_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 3 degreeUnionState62_793 [3,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_793_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_793_oai
