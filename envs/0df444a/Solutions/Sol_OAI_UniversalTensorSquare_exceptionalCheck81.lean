-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck81
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:22:09.288501+00:00
-- url     : https://prove2.me/submissions/45b5b23c-b3ec-405f-bb9b-0b52b9a48d62

import Mathlib
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ExceptionalFourteen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional Fourteen. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma exceptionalCheck81_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows81.length, ∀ c ∈ List.range exceptionalRows81.length,
      refinedCheck 81 10 13 (d+1) (e+1) (a+1) (c+1) exceptionalRows81 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck81_oai := @OAI.UniversalTensorSquare.exceptionalCheck81_oai
