-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_416
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:19.81236+00:00
-- url     : https://prove2.me/submissions/0e9a7cc8-0468-4971-8438-9c73224f732b

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

lemma degreeUnionBranch43_416_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 8 degreeUnionState43_416 [8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_416_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_416_oai
