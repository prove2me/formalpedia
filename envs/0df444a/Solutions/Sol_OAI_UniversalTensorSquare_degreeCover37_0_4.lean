-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCover37_0_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:38:00.4966+00:00
-- url     : https://prove2.me/submissions/d48dc8be-a715-4c1d-9b42-8b7907fa3f1c

import Mathlib
import Definitions.Def_OAIQ259US021

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover37_0_4_oai :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 1 5 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCover37_0_4_oai := @OAI.UniversalTensorSquare.degreeCover37_0_4_oai
