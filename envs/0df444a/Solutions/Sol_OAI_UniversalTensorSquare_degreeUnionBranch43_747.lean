-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_747
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:45:45.65455+00:00
-- url     : https://prove2.me/submissions/3aa76ef9-81b8-4c2e-aaad-55939ae54615

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

lemma degreeUnionBranch43_747_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 25 18 degreeUnionState43_747 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_747_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_747_oai
