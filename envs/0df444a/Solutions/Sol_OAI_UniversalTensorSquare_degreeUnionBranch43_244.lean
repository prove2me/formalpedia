-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_244
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:14.374561+00:00
-- url     : https://prove2.me/submissions/33c464f0-6ee7-4091-ac68-38c410c3424e

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

lemma degreeUnionBranch43_244_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 7 degreeUnionState43_244 [7,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_244_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_244_oai
