-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_334
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:44:59.648371+00:00
-- url     : https://prove2.me/submissions/71bb8790-f20b-4294-96cf-da6435a30365

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

lemma degreeUnionBranch43_334_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 26 degreeUnionState43_334 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_334_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_334_oai
