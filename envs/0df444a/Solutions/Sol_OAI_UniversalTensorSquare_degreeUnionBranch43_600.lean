-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_600
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:25:19.803546+00:00
-- url     : https://prove2.me/submissions/20621b5e-58a3-483e-9c7e-044727e0059d

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

lemma degreeUnionBranch43_600_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 11 32 degreeUnionState43_600 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_600_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_600_oai
