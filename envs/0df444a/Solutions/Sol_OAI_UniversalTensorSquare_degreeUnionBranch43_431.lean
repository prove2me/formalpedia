-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_431
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:07:41.678385+00:00
-- url     : https://prove2.me/submissions/5bcd6122-4169-4982-a0d5-48c62d4423a5

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

lemma degreeUnionBranch43_431_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 12 degreeUnionState43_431 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_431_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_431_oai
