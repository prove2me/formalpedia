-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_301
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:48:58.316823+00:00
-- url     : https://prove2.me/submissions/3baf6516-3573-4989-9c18-5b5dcf2cf5e1

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

lemma degreeUnionBranch62_301_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 5 degreeUnionState62_301 [5,9,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_301_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_301_oai
