-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos110
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:13:41.661196+00:00
-- url     : https://prove2.me/submissions/0b226d8b-6d21-43ec-a69f-e6802dad9421

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck110

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

lemma exceptional_pos110_oai (μ : YoungDiagram) (hμ : μ.card = 110) :
    0 < kronecker (canonicalTableau (candidate 12 8 0) exceptionalCard110)
      (canonicalTableau (candidate 12 8 0) exceptionalCard110) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 16) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard110 exceptionalRows110 (by decide) (by decide) rfl
    exceptionalPlan110 (by decide) (by decide) (by decide) (by decide) exceptionalCheck110 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos110_oai := @OAI.UniversalTensorSquare.exceptional_pos110_oai
