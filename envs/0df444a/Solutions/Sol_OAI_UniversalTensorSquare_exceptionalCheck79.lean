-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck79
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:26:48.879067+00:00
-- url     : https://prove2.me/submissions/770f4ad9-1623-489a-a090-370db6434fed

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

lemma exceptionalCheck79_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows79.length, ∀ c ∈ List.range exceptionalRows79.length,
      refinedCheck 79 10 12 (d+1) (e+1) (a+1) (c+1) exceptionalRows79 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck79_oai := @OAI.UniversalTensorSquare.exceptionalCheck79_oai
