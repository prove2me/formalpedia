-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_664
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:30:21.150806+00:00
-- url     : https://prove2.me/submissions/c09a8034-376f-415a-a1b2-14fa51e3c929

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

lemma degreeUnionBranch43_664_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 20 23 degreeUnionState43_664 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_664_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_664_oai
