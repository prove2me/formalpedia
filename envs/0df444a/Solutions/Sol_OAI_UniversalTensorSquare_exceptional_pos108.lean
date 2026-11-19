-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos108
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:13:35.48666+00:00
-- url     : https://prove2.me/submissions/788e61f2-2d05-436b-a4d5-688e214155f7

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck108

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

lemma exceptional_pos108_oai (μ : YoungDiagram) (hμ : μ.card = 108) :
    0 < kronecker (canonicalTableau (candidate 12 7 1) exceptionalCard108)
      (canonicalTableau (candidate 12 7 1) exceptionalCard108) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 15) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard108 exceptionalRows108 (by decide) (by decide) rfl
    exceptionalPlan108 (by decide) (by decide) (by decide) (by decide) exceptionalCheck108 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos108_oai := @OAI.UniversalTensorSquare.exceptional_pos108_oai
