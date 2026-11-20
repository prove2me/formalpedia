-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos73
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:07:34.454788+00:00
-- url     : https://prove2.me/submissions/0cbc3072-8c91-4a1d-8114-e20c02b98546

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos

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

lemma exceptionalCheck73 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows73.length, ∀ c ∈ List.range exceptionalRows73.length,
      refinedCheck 73 10 9 (d+1) (e+1) (a+1) (c+1) exceptionalRows73 := by
  decide +kernel

lemma exceptional_pos73_oai (μ : YoungDiagram) (hμ : μ.card = 73) :
    0 < kronecker (canonicalTableau (candidate 10 4 1) exceptionalCard73)
      (canonicalTableau (candidate 10 4 1) exceptionalCard73) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 9) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard73 exceptionalRows73 (by decide) (by decide) rfl
    exceptionalPlan73 (by decide) (by decide) (by decide) (by decide) exceptionalCheck73 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos73_oai := @OAI.UniversalTensorSquare.exceptional_pos73_oai
