-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_313
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:09:34.604969+00:00
-- url     : https://prove2.me/submissions/a9fe7a3e-a8a0-414c-a4a8-aa533165718c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_313_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 16 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_313_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_313_oai
