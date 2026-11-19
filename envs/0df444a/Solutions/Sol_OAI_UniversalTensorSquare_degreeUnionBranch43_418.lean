-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_418
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:31.574677+00:00
-- url     : https://prove2.me/submissions/bb813084-3d77-49e8-8e70-b65a8ea4d3b8

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

lemma degreeUnionBranch43_418_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 10 degreeUnionState43_418 [10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_418_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_418_oai
