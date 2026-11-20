-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:26.560589+00:00
-- url     : https://prove2.me/submissions/f52fdf37-cf1e-4b1c-a980-0dfa07a8def5

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

lemma degreeUnionBranch62_44_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 37 11 degreeUnionState62_44 [11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_44_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_44_oai
