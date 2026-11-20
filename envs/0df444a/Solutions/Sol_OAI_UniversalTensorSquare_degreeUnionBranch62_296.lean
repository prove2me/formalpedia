-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_296
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:43:59.139095+00:00
-- url     : https://prove2.me/submissions/d6ffec65-9427-46d8-ae24-b36d886ff626

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

lemma degreeUnionBranch62_296_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 6 degreeUnionState62_296 [6,8,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_296_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_296_oai
