-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_108
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:41:27.513397+00:00
-- url     : https://prove2.me/submissions/90ab2589-8f70-47ff-9dab-1904bde01f98

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_108_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 35 11 degreeUnionState58_108 [11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_108_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_108_oai
