-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_648
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:22:57.037221+00:00
-- url     : https://prove2.me/submissions/3cfd2818-97a4-40af-b120-2e7c40b43e7a

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

lemma degreeUnionBranch62_648_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 4 degreeUnionState62_648 [4,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_648_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_648_oai
