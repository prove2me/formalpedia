-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_878
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:02:48.755888+00:00
-- url     : https://prove2.me/submissions/0a83a96b-5e43-49c6-bdd5-6255a83f72cc

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

lemma degreeUnionBranch62_878_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 4 degreeUnionState62_878 [4,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_878_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_878_oai
