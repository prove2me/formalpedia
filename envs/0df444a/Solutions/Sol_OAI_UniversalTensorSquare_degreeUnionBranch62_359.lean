-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_359
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:27:01.810366+00:00
-- url     : https://prove2.me/submissions/16eed888-72a4-4631-9572-5b434432f704

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

lemma degreeUnionBranch62_359_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 11 degreeUnionState62_359 [11,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_359_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_359_oai
