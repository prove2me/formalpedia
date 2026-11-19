-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck71
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:16:55.223262+00:00
-- url     : https://prove2.me/submissions/66e5c5e0-14d5-489f-b919-522986ec8ea7

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

lemma exceptionalCheck71_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows71.length, ∀ c ∈ List.range exceptionalRows71.length,
      refinedCheck 71 10 8 (d+1) (e+1) (a+1) (c+1) exceptionalRows71 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck71_oai := @OAI.UniversalTensorSquare.exceptionalCheck71_oai
