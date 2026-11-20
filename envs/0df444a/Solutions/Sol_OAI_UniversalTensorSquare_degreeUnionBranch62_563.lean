-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_563
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:49:46.633181+00:00
-- url     : https://prove2.me/submissions/d3cc68fd-8443-4e26-aed2-414d6a35fd57

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

lemma degreeUnionBranch62_563_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 5 degreeUnionState62_563 [5,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_563_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_563_oai
