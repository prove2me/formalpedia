-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_295
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:04:36.297227+00:00
-- url     : https://prove2.me/submissions/1feefb72-36c8-4ee8-b7ad-f52a25effec9

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

lemma degreeUnionBranch39_295_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 13 26 degreeUnionState39_295 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_295_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_295_oai
