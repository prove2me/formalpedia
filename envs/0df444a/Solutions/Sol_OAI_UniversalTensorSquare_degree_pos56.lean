-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos56
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:39:01.83159+00:00
-- url     : https://prove2.me/submissions/da8da422-b230-42f3-83f2-21a7e9792026
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCones56
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos56_oai (μ : YoungDiagram) (hμ : μ.card = 56) :
    0 < kronecker (canonicalTableau (candidate 8 5 0) degreeCard56)
      (canonicalTableau (candidate 8 5 0) degreeCard56) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 10) (by decide) (by decide) rfl (by decide)
    degreeCard56 degreeRows56_0 (by decide) (by decide)
    degreePlan56_0 (by decide) (by decide) (by decide) (by decide) degreeP56 ?_
    degreeCheck56 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard56 rfl degreeCones56
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos56_oai := @OAI.UniversalTensorSquare.degree_pos56_oai
