-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_361
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:27:15.051405+00:00
-- url     : https://prove2.me/submissions/ed36e598-0e1e-4084-b232-c18770a04cea

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

lemma degreeUnionBranch62_361_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 4 degreeUnionState62_361 [4,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_361_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_361_oai
