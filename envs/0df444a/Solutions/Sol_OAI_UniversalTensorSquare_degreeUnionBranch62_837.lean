-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_837
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:50:34.70521+00:00
-- url     : https://prove2.me/submissions/5f06f238-253b-4ab9-8ec4-f0d634daf404

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

lemma degreeUnionBranch62_837_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 6 degreeUnionState62_837 [6,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_837_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_837_oai
