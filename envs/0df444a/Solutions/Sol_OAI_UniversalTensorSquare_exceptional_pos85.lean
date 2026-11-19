-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos85
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:58.117198+00:00
-- url     : https://prove2.me/submissions/26a11925-4028-41b1-b2a6-b1b9fa2967f0

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck85

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

lemma exceptional_pos85_oai (μ : YoungDiagram) (hμ : μ.card = 85) :
    0 < kronecker (canonicalTableau (candidate 10 7 1) exceptionalCard85)
      (canonicalTableau (candidate 10 7 1) exceptionalCard85) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 15) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard85 exceptionalRows85 (by decide) (by decide) rfl
    exceptionalPlan85 (by decide) (by decide) (by decide) (by decide) exceptionalCheck85 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos85_oai := @OAI.UniversalTensorSquare.exceptional_pos85_oai
