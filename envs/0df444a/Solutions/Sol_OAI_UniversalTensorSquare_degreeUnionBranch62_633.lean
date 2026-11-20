-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_633
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:22:09.604254+00:00
-- url     : https://prove2.me/submissions/d4a63a3d-04d4-4f8b-8a85-752acc46b68e

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

lemma degreeUnionBranch62_633_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 5 degreeUnionState62_633 [5,9,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_633_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_633_oai
