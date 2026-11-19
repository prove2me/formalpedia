-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_807
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:11:20.688588+00:00
-- url     : https://prove2.me/submissions/cc4f554d-d754-4a51-94da-80ebfa2b0c63

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

lemma degreeUnionBranch43_807_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 6 37 degreeUnionState43_807 [37] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_807_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_807_oai
