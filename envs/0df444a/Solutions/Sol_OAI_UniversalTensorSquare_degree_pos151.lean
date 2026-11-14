-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos151
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:04:48.393082+00:00
-- url     : https://prove2.me/submissions/d72a4ef6-9fc9-449f-baae-7145db3d9549
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCones151
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos151_oai (μ : YoungDiagram) (hμ : μ.card = 151) :
    0 < kronecker (canonicalTableau (candidate 14 11 1) degreeCard151)
      (canonicalTableau (candidate 14 11 1) degreeCard151) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 23) (by decide) (by decide) rfl (by decide)
    degreeCard151 degreeRows151_0 (by decide) (by decide)
    degreePlan151_0 (by decide) (by decide) (by decide) (by decide) degreeP151 ?_
    degreeCheck151 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard151 rfl degreeCones151
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos151_oai := @OAI.UniversalTensorSquare.degree_pos151_oai
