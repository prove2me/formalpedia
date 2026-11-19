-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_64
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:27:21.715045+00:00
-- url     : https://prove2.me/submissions/19afc8a3-d403-4dcf-bb10-c7ce0fefabc1

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

lemma degreeUnionBranch43_64_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 12 degreeUnionState43_64 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_64_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_64_oai
