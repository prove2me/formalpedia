-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_273
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:40:07.542206+00:00
-- url     : https://prove2.me/submissions/1cf82167-8cd4-4ad0-9986-04605a4c56d4

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_273_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 16 11 degreeUnionState43_273 [11,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_273_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_273_oai
