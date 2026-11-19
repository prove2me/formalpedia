-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_43
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:07:28.211476+00:00
-- url     : https://prove2.me/submissions/81e872fa-753e-4089-9b67-87dede6354fc

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

lemma degreeUnionBranch43_43_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 10 degreeUnionState43_43 [10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_43_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_43_oai
