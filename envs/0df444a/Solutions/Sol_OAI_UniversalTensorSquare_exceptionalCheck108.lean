-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck108
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:21:57.484712+00:00
-- url     : https://prove2.me/submissions/b72acfe7-4443-4583-a98e-af8f2d2f12fb

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

lemma exceptionalCheck108_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows108.length, ∀ c ∈ List.range exceptionalRows108.length,
      refinedCheck 108 12 15 (d+1) (e+1) (a+1) (c+1) exceptionalRows108 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck108_oai := @OAI.UniversalTensorSquare.exceptionalCheck108_oai
