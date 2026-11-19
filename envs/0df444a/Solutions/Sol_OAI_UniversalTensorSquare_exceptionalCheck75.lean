-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck75
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:22:03.286557+00:00
-- url     : https://prove2.me/submissions/7c1d8c02-c5c4-4d1f-9d5a-9345d9594be9

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

lemma exceptionalCheck75_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows75.length, ∀ c ∈ List.range exceptionalRows75.length,
      refinedCheck 75 10 10 (d+1) (e+1) (a+1) (c+1) exceptionalRows75 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck75_oai := @OAI.UniversalTensorSquare.exceptionalCheck75_oai
