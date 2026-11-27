-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_not_isTransverseSliceAt_zero_857b1534e408
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:11.810907+00:00
-- url     : https://prove2.me/submissions/19650985-813a-4de6-837c-658e06715ab4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects

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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    ¬ IsTransverseSliceAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  intro h
  obtain ⟨s, hs, hsX⟩ := h (X 0) (by simp)
  have hbot : sliceIdeal (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 = ⊥ := by
    refine le_bot_iff.mp (sup_le le_rfl ?_)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [linPoly]
  rw [hbot, Ideal.mem_bot, mul_eq_zero] at hsX
  rcases hsX with h0 | h0
  · exact hs (by rw [h0, map_zero])
  · exact X_ne_zero 0 h0
end GroundTheory.Heights₂.Heights
