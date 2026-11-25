-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_genPt_bot_zero_ne_zero_2941ae6aaa72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:59.394301+00:00
-- url     : https://prove2.me/submissions/9577f786-89a1-480b-afef-225f05be1fc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0 ≠ 0 := by
  unfold genPt
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero 0
end GroundTheory.Heights₂.Heights
