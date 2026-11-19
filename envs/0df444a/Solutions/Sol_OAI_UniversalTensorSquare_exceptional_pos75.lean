-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos75
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:33.168932+00:00
-- url     : https://prove2.me/submissions/d70cc2a1-73a1-4470-9440-a4b538b2f282

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck75

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

lemma exceptional_pos75_oai (μ : YoungDiagram) (hμ : μ.card = 75) :
    0 < kronecker (canonicalTableau (candidate 10 5 0) exceptionalCard75)
      (canonicalTableau (candidate 10 5 0) exceptionalCard75) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 10) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard75 exceptionalRows75 (by decide) (by decide) rfl
    exceptionalPlan75 (by decide) (by decide) (by decide) (by decide) exceptionalCheck75 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos75_oai := @OAI.UniversalTensorSquare.exceptional_pos75_oai
