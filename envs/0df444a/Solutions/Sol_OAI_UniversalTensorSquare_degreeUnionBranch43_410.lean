-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_410
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:02:43.413918+00:00
-- url     : https://prove2.me/submissions/0462442e-b517-4074-b21f-ef2d954c1b45

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

lemma degreeUnionBranch43_410_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 12 degreeUnionState43_410 [12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_410_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_410_oai
