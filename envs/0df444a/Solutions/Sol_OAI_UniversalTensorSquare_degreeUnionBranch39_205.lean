-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_205
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:52:14.625087+00:00
-- url     : https://prove2.me/submissions/942e9e1d-c5da-49a9-9dc2-e55e48284381

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_205_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 20 19 degreeUnionState39_205 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_205_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_205_oai
