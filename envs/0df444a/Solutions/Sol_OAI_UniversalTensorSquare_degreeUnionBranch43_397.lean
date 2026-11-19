-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_397
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:07.498003+00:00
-- url     : https://prove2.me/submissions/95faf213-4d00-4964-8450-4738cbedb600

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

lemma degreeUnionBranch43_397_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 8 degreeUnionState43_397 [8,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_397_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_397_oai
