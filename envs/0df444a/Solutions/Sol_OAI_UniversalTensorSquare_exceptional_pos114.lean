-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos114
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:13.88367+00:00
-- url     : https://prove2.me/submissions/b3a27b7b-5612-475f-83f6-8ac1071e7c41

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck114

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

lemma exceptional_pos114_oai (μ : YoungDiagram) (hμ : μ.card = 114) :
    0 < kronecker (canonicalTableau (candidate 12 9 0) exceptionalCard114)
      (canonicalTableau (candidate 12 9 0) exceptionalCard114) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 18) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard114 exceptionalRows114 (by decide) (by decide) rfl
    exceptionalPlan114 (by decide) (by decide) (by decide) (by decide) exceptionalCheck114 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos114_oai := @OAI.UniversalTensorSquare.exceptional_pos114_oai
