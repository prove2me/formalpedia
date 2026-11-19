-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos79
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:39.243995+00:00
-- url     : https://prove2.me/submissions/4f8542ab-2745-4af2-9149-e417562f0392

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck79

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

lemma exceptional_pos79_oai (μ : YoungDiagram) (hμ : μ.card = 79) :
    0 < kronecker (canonicalTableau (candidate 10 6 0) exceptionalCard79)
      (canonicalTableau (candidate 10 6 0) exceptionalCard79) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 12) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard79 exceptionalRows79 (by decide) (by decide) rfl
    exceptionalPlan79 (by decide) (by decide) (by decide) (by decide) exceptionalCheck79 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos79_oai := @OAI.UniversalTensorSquare.exceptional_pos79_oai
