-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCover37_0_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:37:48.920383+00:00
-- url     : https://prove2.me/submissions/b8c4ffb1-e0ef-4caa-b849-0f3b73557658

import Mathlib
import Definitions.Def_OAIQ259US021

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover37_0_2_oai :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 1 3 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCover37_0_2_oai := @OAI.UniversalTensorSquare.degreeCover37_0_2_oai
