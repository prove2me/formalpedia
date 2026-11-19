-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck110
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T18:51:06.670445+00:00
-- url     : https://prove2.me/submissions/4dd1c603-0a6c-4dfd-bb10-b807ea154f8b

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

lemma exceptionalCheck110_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows110.length, ∀ c ∈ List.range exceptionalRows110.length,
      refinedCheck 110 12 16 (d+1) (e+1) (a+1) (c+1) exceptionalRows110 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck110_oai := @OAI.UniversalTensorSquare.exceptionalCheck110_oai
