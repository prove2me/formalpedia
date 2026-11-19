-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:39:55.599332+00:00
-- url     : https://prove2.me/submissions/21983d6a-cdcd-40b2-b246-ca169387ad9a

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

lemma degreeUnionBranch43_27_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 24 9 degreeUnionState43_27 [9,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_27_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_27_oai
