-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos33
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:17.569109+00:00
-- url     : https://prove2.me/submissions/13acbf81-70d0-4c52-887b-9005d5a4e033
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck33
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones33 : ∀ q ∈ degreeQs33, ∀ μ : YoungDiagram, μ.card = 33 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 3 0) μ := by
  intro q hq
  simp only [degreeQs33,List.not_mem_nil] at hq

lemma degree_pos33_oai (μ : YoungDiagram) (hμ : μ.card = 33) :
    0 < kronecker (canonicalTableau (candidate 6 3 0) degreeCard33)
      (canonicalTableau (candidate 6 3 0) degreeCard33) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 6) (by decide) (by decide) rfl (by decide)
    degreeCard33 degreeRows33_0 (by decide) (by decide)
    degreePlan33_0 (by decide) (by decide) (by decide) (by decide) degreeP33 ?_
    degreeCheck33 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard33 rfl degreeCones33
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos33_oai := @OAI.UniversalTensorSquare.degree_pos33_oai
