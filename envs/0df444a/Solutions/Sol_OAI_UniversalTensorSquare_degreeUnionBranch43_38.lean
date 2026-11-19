-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_38
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:54:03.349407+00:00
-- url     : https://prove2.me/submissions/d66c3542-7df4-4dfa-86b3-7c84dd416db1

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

lemma degreeUnionBranch43_38_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 26 5 degreeUnionState43_38 [5,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_38_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_38_oai
