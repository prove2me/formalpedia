-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos54
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:40:57.10953+00:00
-- url     : https://prove2.me/submissions/282aab63-759b-4448-8800-298abca92fdd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCones54
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos54_oai (μ : YoungDiagram) (hμ : μ.card = 54) :
    0 < kronecker (canonicalTableau (candidate 8 4 1) degreeCard54)
      (canonicalTableau (candidate 8 4 1) degreeCard54) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 9) (by decide) (by decide) rfl (by decide)
    degreeCard54 degreeRows54_0 (by decide) (by decide)
    degreePlan54_0 (by decide) (by decide) (by decide) (by decide) degreeP54 ?_
    degreeCheck54 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard54 rfl degreeCones54
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos54_oai := @OAI.UniversalTensorSquare.degree_pos54_oai
