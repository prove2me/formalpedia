-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_730
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:00:30.326342+00:00
-- url     : https://prove2.me/submissions/ea6350c6-575a-4abb-a80e-469f096cf660

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

lemma degreeUnionBranch62_730_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 7 degreeUnionState62_730 [7,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_730_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_730_oai
