-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos71
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:27.023287+00:00
-- url     : https://prove2.me/submissions/d03dea0b-f0f9-463b-84b2-c6b02a8a4b73

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck71

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

lemma exceptional_pos71_oai (μ : YoungDiagram) (hμ : μ.card = 71) :
    0 < kronecker (canonicalTableau (candidate 10 4 0) exceptionalCard71)
      (canonicalTableau (candidate 10 4 0) exceptionalCard71) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 8) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard71 exceptionalRows71 (by decide) (by decide) rfl
    exceptionalPlan71 (by decide) (by decide) (by decide) (by decide) exceptionalCheck71 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos71_oai := @OAI.UniversalTensorSquare.exceptional_pos71_oai
