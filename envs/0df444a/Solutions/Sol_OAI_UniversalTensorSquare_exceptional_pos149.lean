-- Prove2me | solution 1 for OAI.UniversalTensorSquare.exceptional_pos149
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:20.41041+00:00
-- url     : https://prove2.me/submissions/31a0954e-4577-41ac-b6e7-7c6ec38a12f7

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
import Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck149

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

lemma exceptional_pos149_oai (μ : YoungDiagram) (hμ : μ.card = 149) :
    0 < kronecker (canonicalTableau (candidate 14 11 0) exceptionalCard149)
      (canonicalTableau (candidate 14 11 0) exceptionalCard149) (canonicalTableau μ hμ) := by
  apply candidate_refined_pos (r := 22) (by decide) (by decide) (by decide) rfl
    (by decide) exceptionalCard149 exceptionalRows149 (by decide) (by decide) rfl
    exceptionalPlan149 (by decide) (by decide) (by decide) (by decide) exceptionalCheck149 μ hμ

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.exceptional_pos149_oai := @OAI.UniversalTensorSquare.exceptional_pos149_oai
