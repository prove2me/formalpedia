-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_X_zero_one_dvd_sub_substZeroOne_0e2e6d7fe4f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:57.873378+00:00
-- url     : https://prove2.me/submissions/4edf1277-82c4-420c-b0a1-102122139c97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax

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
theorem _root_.solution (g : MvPolynomial (Fin 1 × Fin 2) ℚ) : X (0, 1) ∣ g - substZeroOne g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [substZeroOne]
  | add p q hp hq =>
    have e : p + q - substZeroOne (p + q) = (p - substZeroOne p) + (q - substZeroOne q) := by
      simp only [map_add]; ring
    rw [e]; exact dvd_add hp hq
  | mul_X p i hp =>
    have e : p * X i - substZeroOne (p * X i) =
        (p - substZeroOne p) * X i + substZeroOne p * (X i - substZeroOne (X i)) := by
      simp only [map_mul]; ring
    rw [e]
    refine dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)
    by_cases hi : i = (0, 1)
    · subst hi; simp [substZeroOne]
    · simp [substZeroOne, hi]
end GroundTheory.Heights₂.Heights
