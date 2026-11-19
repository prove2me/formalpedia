-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_367
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:53:10.355106+00:00
-- url     : https://prove2.me/submissions/0628725a-ee3f-466f-a1a1-bda6f282b255

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

lemma degreeUnionBranch43_367_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 30 4 degreeUnionState43_367 [4,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_367_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_367_oai
