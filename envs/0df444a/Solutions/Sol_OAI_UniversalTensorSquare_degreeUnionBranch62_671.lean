-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_671
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:33:04.04432+00:00
-- url     : https://prove2.me/submissions/4fb4dbdb-eff3-44ed-ab9b-7168af6fbfc1

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

lemma degreeUnionBranch62_671_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 3 degreeUnionState62_671 [3,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_671_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_671_oai
