-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:35.962904+00:00
-- url     : https://prove2.me/submissions/d2a1acc3-7837-45ea-a8c0-9b4529132ecc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChowFormSwap
theorem _root_.solution :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  isChowForm_point ℚ
end ChowFormSwap
end GroundTheory.Heights₂.Heights
