-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:38:56.833851+00:00
-- url     : https://prove2.me/submissions/43fde50b-d278-43c0-854f-98a4846d623c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCone50_1
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones50 : ∀ q ∈ degreeQs50, ∀ μ : YoungDiagram, μ.card = 50 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 3 1) μ := by
  intro q hq
  simp only [degreeQs50,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone50_1

lemma degree_pos50_oai (μ : YoungDiagram) (hμ : μ.card = 50) :
    0 < kronecker (canonicalTableau (candidate 8 3 1) degreeCard50)
      (canonicalTableau (candidate 8 3 1) degreeCard50) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 7) (by decide) (by decide) rfl (by decide)
    degreeCard50 degreeRows50_0 (by decide) (by decide)
    degreePlan50_0 (by decide) (by decide) (by decide) (by decide) degreeP50 ?_
    degreeCheck50 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard50 rfl degreeCones50
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos50_oai := @OAI.UniversalTensorSquare.degree_pos50_oai
