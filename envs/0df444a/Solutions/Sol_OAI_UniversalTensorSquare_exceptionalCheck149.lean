-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck149
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T18:51:17.71314+00:00
-- url     : https://prove2.me/submissions/cc898053-2a94-4d3b-86ce-79059deae1a3

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

lemma exceptionalCheck149_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows149.length, ∀ c ∈ List.range exceptionalRows149.length,
      refinedCheck 149 14 22 (d+1) (e+1) (a+1) (c+1) exceptionalRows149 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck149_oai := @OAI.UniversalTensorSquare.exceptionalCheck149_oai
