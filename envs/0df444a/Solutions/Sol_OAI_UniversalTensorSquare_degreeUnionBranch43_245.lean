-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_245
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:20.111354+00:00
-- url     : https://prove2.me/submissions/1c003bb7-7ff4-4538-9fcb-2b2df28f3065

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

lemma degreeUnionBranch43_245_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 8 degreeUnionState43_245 [8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_245_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_245_oai
