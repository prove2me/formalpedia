-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:14:18.094813+00:00
-- url     : https://prove2.me/submissions/c3f24e94-35c6-4df2-8f64-1f93ee91a4ca

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

lemma degreeUnionBranch62_24_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 40 10 degreeUnionState62_24 [10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_24_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_24_oai
