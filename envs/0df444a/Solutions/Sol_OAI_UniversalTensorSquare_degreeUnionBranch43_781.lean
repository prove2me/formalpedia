-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_781
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:00:37.752222+00:00
-- url     : https://prove2.me/submissions/d9da630e-9da0-4e3d-8c5b-d04f0c62d7df

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

lemma degreeUnionBranch43_781_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 32 11 degreeUnionState43_781 [11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_781_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_781_oai
