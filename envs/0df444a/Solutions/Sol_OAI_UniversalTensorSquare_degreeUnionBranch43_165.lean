-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_165
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:18:56.517942+00:00
-- url     : https://prove2.me/submissions/d834a7a6-8044-4910-bbe9-ffabbabfce67

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

lemma degreeUnionBranch43_165_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 26 degreeUnionState43_165 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_165_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_165_oai
