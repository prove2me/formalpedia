-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_830
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:22:07.677203+00:00
-- url     : https://prove2.me/submissions/f4fdaa34-da22-4c3e-87a0-186cf9997380

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

lemma degreeUnionBranch43_830_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 24 19 degreeUnionState43_830 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_830_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_830_oai
