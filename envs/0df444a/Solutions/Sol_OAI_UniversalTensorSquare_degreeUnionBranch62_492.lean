-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_492
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:43:13.659683+00:00
-- url     : https://prove2.me/submissions/edbfe3f8-6c7e-4aef-8399-e05ad112b096

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

lemma degreeUnionBranch62_492_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 8 degreeUnionState62_492 [8,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_492_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_492_oai
