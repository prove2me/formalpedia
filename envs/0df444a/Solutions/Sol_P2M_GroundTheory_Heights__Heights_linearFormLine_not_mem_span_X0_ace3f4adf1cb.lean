-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:38.471223+00:00
-- url     : https://prove2.me/submissions/c145fa28-fc3b-41a8-bb3c-7e91e09f5678

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
theorem _root_.solution : linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} := by
  rw [linForm_tLine, Ideal.mem_span_singleton, X_dvd_X]
  decide
end GroundTheory.Heights₂.Heights
