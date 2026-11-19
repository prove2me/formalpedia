-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:37.597196+00:00
-- url     : https://prove2.me/submissions/db4e4321-b1f6-4b23-aa99-f0bde0cc6210

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

lemma degreeUnionBranch43_2_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 2 43 42 degreeHalfRegions43 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_2_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_2_oai
