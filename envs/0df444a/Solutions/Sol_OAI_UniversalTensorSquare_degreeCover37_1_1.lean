-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCover37_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:38:12.143907+00:00
-- url     : https://prove2.me/submissions/9e844952-60d9-48e5-8827-9adfcbabdbd8

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

lemma degreeCover37_1_1_oai :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 2 2 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCover37_1_1_oai := @OAI.UniversalTensorSquare.degreeCover37_1_1_oai
