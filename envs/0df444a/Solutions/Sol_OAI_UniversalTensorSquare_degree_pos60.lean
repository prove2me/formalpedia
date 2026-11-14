-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos60
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:37:51.183526+00:00
-- url     : https://prove2.me/submissions/00cc5c3e-3f90-45e0-992d-3f85caf28249
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCones60
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos60_oai (μ : YoungDiagram) (hμ : μ.card = 60) :
    0 < kronecker (canonicalTableau (candidate 8 6 0) degreeCard60)
      (canonicalTableau (candidate 8 6 0) degreeCard60) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 12) (by decide) (by decide) rfl (by decide)
    degreeCard60 degreeRows60_0 (by decide) (by decide)
    degreePlan60_0 (by decide) (by decide) (by decide) (by decide) degreeP60 ?_
    degreeCheck60 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard60 rfl degreeCones60
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos60_oai := @OAI.UniversalTensorSquare.degree_pos60_oai
