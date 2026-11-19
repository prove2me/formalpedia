-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_161
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:15:31.963908+00:00
-- url     : https://prove2.me/submissions/db400ea0-cad1-4b97-8b4f-2285fe038e32

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

lemma degreeUnionBranch43_161_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 22 degreeUnionState43_161 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_161_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_161_oai
