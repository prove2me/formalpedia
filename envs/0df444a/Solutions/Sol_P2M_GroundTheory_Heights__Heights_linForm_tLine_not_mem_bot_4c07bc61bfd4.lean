-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:37.643848+00:00
-- url     : https://prove2.me/submissions/f14d465d-7648-4390-b2ef-b701220c08e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_tLine_1098a18ec0be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open LineChowForm
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) := by
  rw [linForm_tLine, Ideal.mem_bot]
  exact X_ne_zero 1
end GroundTheory.Heights₂.Heights
