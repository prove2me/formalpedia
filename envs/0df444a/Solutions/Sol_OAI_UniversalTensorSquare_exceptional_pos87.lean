-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos87
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:18:04.08233+00:00
-- url     : https://prove2.me/submissions/b838fe9e-6142-4891-87c8-9ef059cc9771

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck87

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

lemma exceptional_pos87_oai (μ : YoungDiagram) (hμ : μ.card = 87) :
    0 < kronecker (canonicalTableau (candidate 10 8 0) exceptionalCard87)
      (canonicalTableau (candidate 10 8 0) exceptionalCard87) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 16) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard87 exceptionalRows87 (by decide) (by decide) rfl
    exceptionalPlan87 (by decide) (by decide) (by decide) (by decide) exceptionalCheck87 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos87_oai := @OAI.UniversalTensorSquare.exceptional_pos87_oai
