-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck85
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:22:20.669239+00:00
-- url     : https://prove2.me/submissions/95c6381f-d94e-409a-a005-5a49bcc58484

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

lemma exceptionalCheck85_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows85.length, ∀ c ∈ List.range exceptionalRows85.length,
      refinedCheck 85 10 15 (d+1) (e+1) (a+1) (c+1) exceptionalRows85 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck85_oai := @OAI.UniversalTensorSquare.exceptionalCheck85_oai
