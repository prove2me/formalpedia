-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:07:41.206862+00:00
-- url     : https://prove2.me/submissions/122344fb-1575-485a-a3ad-701f48af16c8

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

lemma exceptionalCheck77 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows77.length, ∀ c ∈ List.range exceptionalRows77.length,
      refinedCheck 77 10 11 (d+1) (e+1) (a+1) (c+1) exceptionalRows77 := by
  decide +kernel

lemma exceptional_pos77_oai (μ : YoungDiagram) (hμ : μ.card = 77) :
    0 < kronecker (canonicalTableau (candidate 10 5 1) exceptionalCard77)
      (canonicalTableau (candidate 10 5 1) exceptionalCard77) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 11) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard77 exceptionalRows77 (by decide) (by decide) rfl
    exceptionalPlan77 (by decide) (by decide) (by decide) (by decide) exceptionalCheck77 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos77_oai := @OAI.UniversalTensorSquare.exceptional_pos77_oai
