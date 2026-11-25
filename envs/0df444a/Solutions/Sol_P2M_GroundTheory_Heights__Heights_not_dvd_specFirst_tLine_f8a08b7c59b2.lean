-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:33.049189+00:00
-- url     : https://prove2.me/submissions/84714b3c-dbb7-41a6-985a-70b36711a8ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_specialize_det_lineForm_eq_a195f3e197c2

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
theorem _root_.solution :
    ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine := by
  rw [specialize_det_lineForm_eq, dvd_neg, qLine, X_dvd_X]
  decide
end GroundTheory.Heights₂.Heights
