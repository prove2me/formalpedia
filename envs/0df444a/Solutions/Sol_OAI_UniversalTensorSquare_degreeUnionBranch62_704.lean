-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_704
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:54:20.581346+00:00
-- url     : https://prove2.me/submissions/d1157e88-d3d7-4551-bd60-45f0fabf36fc

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

lemma degreeUnionBranch62_704_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 10 degreeUnionState62_704 [10,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_704_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_704_oai
