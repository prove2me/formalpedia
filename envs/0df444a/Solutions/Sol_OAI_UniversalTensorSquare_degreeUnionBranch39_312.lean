-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_312
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:13:52.073552+00:00
-- url     : https://prove2.me/submissions/832f610b-98f7-4492-ae45-411ff9bd48ab

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

lemma degreeUnionBranch39_312_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 15 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_312_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_312_oai
