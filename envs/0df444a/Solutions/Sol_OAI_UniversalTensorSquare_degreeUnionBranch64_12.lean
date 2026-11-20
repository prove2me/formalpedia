-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:01:33.323415+00:00
-- url     : https://prove2.me/submissions/9a16a91a-717b-41fc-844e-6ac33c2c595d

import Mathlib
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 64. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch64_12_oai : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 12 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch64_12_oai := @OAI.UniversalTensorSquare.degreeUnionBranch64_12_oai
