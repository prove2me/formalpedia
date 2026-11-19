-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos83
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:51.318766+00:00
-- url     : https://prove2.me/submissions/e81f7d28-6d1b-4806-b4d6-fd849f80377c

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck83

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

lemma exceptional_pos83_oai (μ : YoungDiagram) (hμ : μ.card = 83) :
    0 < kronecker (canonicalTableau (candidate 10 7 0) exceptionalCard83)
      (canonicalTableau (candidate 10 7 0) exceptionalCard83) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 14) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard83 exceptionalRows83 (by decide) (by decide) rfl
    exceptionalPlan83 (by decide) (by decide) (by decide) (by decide) exceptionalCheck83 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos83_oai := @OAI.UniversalTensorSquare.exceptional_pos83_oai
