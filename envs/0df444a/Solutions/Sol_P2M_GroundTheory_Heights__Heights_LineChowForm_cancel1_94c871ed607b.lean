-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_cancel1_94c871ed607b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:37.2978+00:00
-- url     : https://prove2.me/submissions/5f3c0ac6-35f5-4f8d-b19d-abb94decd9a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_X_dvd_of_substZeroZeroZero_eq_zero_e00626ca4948

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
theorem _root_.solution (h q : MvPolynomial (Fin 2 × Fin 2) F) (e : X (0,0) * h = D2 * q) : D2 ∣ h := by
  have e0 := congrArg substZeroZeroZero e
  have hz : substZeroZeroZero (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by simp [substZeroZeroZero]
  have hD : substZeroZeroZero (D2 : MvPolynomial (Fin 2 × Fin 2) F) = -(X (0,1) * X (1,0)) := by
    simp [substZeroZeroZero, D2]
  rw [map_mul, map_mul, hz, hD, zero_mul] at e0
  have hne : -(X (0,1) * X (1,0)) ≠ (0 : MvPolynomial (Fin 2 × Fin 2) F) :=
    neg_ne_zero.mpr (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  have hq : substZeroZeroZero q = 0 := by
    rcases mul_eq_zero.mp e0.symm with h' | h'
    · exact absurd h' hne
    · exact h'
  obtain ⟨q', rfl⟩ := X_dvd_of_substZeroZeroZero_eq_zero q hq
  refine ⟨q', mul_left_cancel₀ (X_ne_zero ((0 : Fin 2),(0 : Fin 2))) ?_⟩
  rw [e]; ring
end GroundTheory.Heights₂.Heights.LineChowForm
