-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptionalCheck83
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:22:14.975298+00:00
-- url     : https://prove2.me/submissions/a14b029d-fd83-49ac-aebc-700f2fc204b5

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

lemma exceptionalCheck83_oai : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows83.length, ∀ c ∈ List.range exceptionalRows83.length,
      refinedCheck 83 10 14 (d+1) (e+1) (a+1) (c+1) exceptionalRows83 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptionalCheck83_oai := @OAI.UniversalTensorSquare.exceptionalCheck83_oai
