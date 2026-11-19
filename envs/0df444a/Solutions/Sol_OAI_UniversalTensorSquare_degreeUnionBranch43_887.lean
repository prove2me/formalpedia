-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_887
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:32:13.484064+00:00
-- url     : https://prove2.me/submissions/4e5e7a8e-a880-426d-ba5e-caf4e4408395

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

lemma degreeUnionBranch43_887_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 8 35 degreeUnionState43_887 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_887_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_887_oai
