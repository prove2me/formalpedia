-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_827
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:16:43.414999+00:00
-- url     : https://prove2.me/submissions/77f8aff0-8477-43fe-828a-f4648a931c6d

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

lemma degreeUnionBranch43_827_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 27 16 degreeUnionState43_827 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_827_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_827_oai
