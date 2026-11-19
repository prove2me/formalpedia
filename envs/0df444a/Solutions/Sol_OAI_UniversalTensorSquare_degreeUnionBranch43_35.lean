-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:49:07.126665+00:00
-- url     : https://prove2.me/submissions/d70ed019-1aa1-4a25-97e8-a29f416a4af0

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

lemma degreeUnionBranch43_35_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 22 10 degreeUnionState43_35 [10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_35_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_35_oai
