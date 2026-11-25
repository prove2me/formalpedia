-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_X_dvd_of_substZeroZeroZero_eq_zero_e00626ca4948
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:10.279858+00:00
-- url     : https://prove2.me/submissions/95379718-d019-42a9-9c56-354b45a6b4ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant

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
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.LineChowForm
theorem _root_.solution (q : MvPolynomial (Fin 2 × Fin 2) F) (h : substZeroZeroZero q = 0) : X (0,0) ∣ q := by
  have key : ∀ q : MvPolynomial (Fin 2 × Fin 2) F, X (0,0) ∣ q - substZeroZeroZero q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [substZeroZeroZero]
    | add p q hp hq =>
      have e : p + q - substZeroZeroZero (p+q) = (p - substZeroZeroZero p) + (q - substZeroZeroZero q) := by
        simp only [map_add]; ring
      rw [e]; exact dvd_add hp hq
    | mul_X p i hp =>
      have e : p * X i - substZeroZeroZero (p * X i) =
          (p - substZeroZeroZero p) * X i + substZeroZeroZero p * (X i - substZeroZeroZero (X i)) := by
        simp only [map_mul]; ring
      rw [e]
      refine dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)
      by_cases hi : i = (0,0)
      · subst hi; simp [substZeroZeroZero]
      · simp [substZeroZeroZero, hi]
  simpa [h] using key q
end GroundTheory.Heights₂.Heights.LineChowForm
