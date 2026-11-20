-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_876
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:08:06.425545+00:00
-- url     : https://prove2.me/submissions/e1c74571-ab0c-42ff-b04b-20ae29d6078a

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

lemma degreeUnionBranch62_876_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 9 degreeUnionState62_876 [9,9,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_876_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_876_oai
