-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_720
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:40:32.966256+00:00
-- url     : https://prove2.me/submissions/91fb927b-98bc-414b-87fb-abc0df7c8dbd

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

lemma degreeUnionBranch43_720_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 12 31 degreeUnionState43_720 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_720_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_720_oai
