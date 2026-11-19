-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos106
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:13:29.477684+00:00
-- url     : https://prove2.me/submissions/ef5ac93f-cfcd-4211-9653-73da3e3c35d2

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck106

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

lemma exceptional_pos106_oai (μ : YoungDiagram) (hμ : μ.card = 106) :
    0 < kronecker (canonicalTableau (candidate 12 7 0) exceptionalCard106)
      (canonicalTableau (candidate 12 7 0) exceptionalCard106) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 14) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard106 exceptionalRows106 (by decide) (by decide) rfl
    exceptionalPlan106 (by decide) (by decide) (by decide) (by decide) exceptionalCheck106 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos106_oai := @OAI.UniversalTensorSquare.exceptional_pos106_oai
