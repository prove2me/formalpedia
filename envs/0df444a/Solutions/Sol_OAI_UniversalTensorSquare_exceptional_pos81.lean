-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos81
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:45.309758+00:00
-- url     : https://prove2.me/submissions/e8ea2186-d51d-4011-89ae-eda64b4a97f2

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck81

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

lemma exceptional_pos81_oai (μ : YoungDiagram) (hμ : μ.card = 81) :
    0 < kronecker (canonicalTableau (candidate 10 6 1) exceptionalCard81)
      (canonicalTableau (candidate 10 6 1) exceptionalCard81) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 13) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard81 exceptionalRows81 (by decide) (by decide) rfl
    exceptionalPlan81 (by decide) (by decide) (by decide) (by decide) exceptionalCheck81 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos81_oai := @OAI.UniversalTensorSquare.exceptional_pos81_oai
