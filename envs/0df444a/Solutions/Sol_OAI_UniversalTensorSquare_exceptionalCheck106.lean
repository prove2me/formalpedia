-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck106
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T18:51:01.305073+00:00
-- url     : https://prove2.me/submissions/b73d375d-8629-4a2d-9181-2a342d1909ea

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

lemma exceptionalCheck106_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows106.length, ∀ c ∈ List.range exceptionalRows106.length,
      refinedCheck 106 12 14 (d+1) (e+1) (a+1) (c+1) exceptionalRows106 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck106_oai := @OAI.UniversalTensorSquare.exceptionalCheck106_oai
