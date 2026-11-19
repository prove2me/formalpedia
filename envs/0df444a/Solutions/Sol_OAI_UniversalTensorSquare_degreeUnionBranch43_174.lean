-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_174
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:19:49.995677+00:00
-- url     : https://prove2.me/submissions/1b389645-ffd9-40a4-9185-48de6f2c1a9b

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

lemma degreeUnionBranch43_174_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 8 35 degreeUnionState43_174 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_174_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_174_oai
