-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_164
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:18:50.810333+00:00
-- url     : https://prove2.me/submissions/758a0438-863c-4130-a971-1a671c38d8af

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

lemma degreeUnionBranch43_164_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 25 degreeUnionState43_164 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_164_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_164_oai
