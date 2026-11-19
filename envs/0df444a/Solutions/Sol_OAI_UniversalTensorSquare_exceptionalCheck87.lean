-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck87
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:22:26.508578+00:00
-- url     : https://prove2.me/submissions/b90849c7-b6ae-4865-b5fa-89b1375ce2a7

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

lemma exceptionalCheck87_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows87.length, ∀ c ∈ List.range exceptionalRows87.length,
      refinedCheck 87 10 16 (d+1) (e+1) (a+1) (c+1) exceptionalRows87 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck87_oai := @OAI.UniversalTensorSquare.exceptionalCheck87_oai
