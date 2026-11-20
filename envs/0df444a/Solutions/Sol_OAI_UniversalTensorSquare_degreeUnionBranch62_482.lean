-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_482
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:38:32.610215+00:00
-- url     : https://prove2.me/submissions/3bf768c7-a2b9-4813-bcb5-1a1b927695c8

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

lemma degreeUnionBranch62_482_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 11 degreeUnionState62_482 [11,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_482_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_482_oai
