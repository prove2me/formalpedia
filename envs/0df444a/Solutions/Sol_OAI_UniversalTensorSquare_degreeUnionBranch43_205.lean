-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_205
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:25:01.547534+00:00
-- url     : https://prove2.me/submissions/eaab3d6c-93d1-4cdf-afb6-3366a51572e8

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

lemma degreeUnionBranch43_205_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 27 6 degreeUnionState43_205 [6,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_205_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_205_oai
