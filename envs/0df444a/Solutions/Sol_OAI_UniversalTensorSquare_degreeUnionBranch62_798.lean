-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_798
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:24:03.570605+00:00
-- url     : https://prove2.me/submissions/a61761ec-2023-4924-8d95-45f4acc7e750

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

lemma degreeUnionBranch62_798_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 8 degreeUnionState62_798 [8,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_798_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_798_oai
