-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_419
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:37.497788+00:00
-- url     : https://prove2.me/submissions/cad28cb0-1634-4419-bc45-3ef3733ae600

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

lemma degreeUnionBranch43_419_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 11 degreeUnionState43_419 [11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_419_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_419_oai
