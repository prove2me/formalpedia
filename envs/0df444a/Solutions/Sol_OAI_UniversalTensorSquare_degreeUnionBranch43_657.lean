-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_657
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:29:32.726593+00:00
-- url     : https://prove2.me/submissions/be9cd38a-ad7c-44d0-8aa1-3ca6de9556e6

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

lemma degreeUnionBranch43_657_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 27 16 degreeUnionState43_657 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_657_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_657_oai
