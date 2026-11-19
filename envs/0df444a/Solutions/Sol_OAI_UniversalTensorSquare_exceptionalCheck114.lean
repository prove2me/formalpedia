-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck114
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T18:51:12.087502+00:00
-- url     : https://prove2.me/submissions/199de9f5-b1bf-47c9-ad5a-0783baadc54f

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

lemma exceptionalCheck114_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows114.length, ∀ c ∈ List.range exceptionalRows114.length,
      refinedCheck 114 12 18 (d+1) (e+1) (a+1) (c+1) exceptionalRows114 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck114_oai := @OAI.UniversalTensorSquare.exceptionalCheck114_oai
