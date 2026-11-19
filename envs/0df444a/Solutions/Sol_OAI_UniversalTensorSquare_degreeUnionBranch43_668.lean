-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_668
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:30:46.182718+00:00
-- url     : https://prove2.me/submissions/e0034301-beeb-4c2b-90ad-f3158455f886

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

lemma degreeUnionBranch43_668_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 16 27 degreeUnionState43_668 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_668_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_668_oai
