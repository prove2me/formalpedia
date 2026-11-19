-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_770
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:55:24.047195+00:00
-- url     : https://prove2.me/submissions/e52d7287-8bc8-4488-bd29-01c5927a7724

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

lemma degreeUnionBranch43_770_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 2 41 degreeUnionState43_770 [41] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_770_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_770_oai
