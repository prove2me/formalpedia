-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_224
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:30:02.41677+00:00
-- url     : https://prove2.me/submissions/94a99ad9-d5ae-476d-b176-73d2baab1a07

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

lemma degreeUnionBranch43_224_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 8 degreeUnionState43_224 [8,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_224_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_224_oai
