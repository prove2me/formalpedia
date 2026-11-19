-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_305
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:05:40.887633+00:00
-- url     : https://prove2.me/submissions/6c81d448-145a-4b8e-8630-d536e4609b93

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

lemma degreeUnionBranch39_305_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 3 36 degreeUnionState39_305 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_305_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_305_oai
