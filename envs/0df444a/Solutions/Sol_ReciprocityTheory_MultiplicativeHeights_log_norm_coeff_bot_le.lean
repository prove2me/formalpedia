-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_bot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:52:27.787744+00:00
-- url     : https://prove2.me/submissions/5b30b79f-31f2-44a3-b081-7545807a0881

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (hbot : ∀ k', k' < k → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hbot
  have hp : p ≠ 0 := fun h => hk (by simp [h])
  have hq0 : q ≠ 0 := fun h => hp (by simp [hq, h])
  have hc : p.coeff k = q.coeff 0 := by
    rw [hq, coeff_X_pow_mul']; simp
  have hM : p.logMahlerMeasure = q.logMahlerMeasure := by
    rw [hq, logMahlerMeasure_mul_eq_add_logMahlerMeasure (by rw [← hq]; exact hp),
      X_pow_eq_monomial, logMahlerMeasure_monomial]
    simp
  rw [hc, hM, logMahlerMeasure_eq_log_MahlerMeasure]
  rw [hc] at hk
  apply Real.log_le_log (norm_pos_iff.mpr hk)
  simpa using norm_coeff_le_choose_mul_mahlerMeasure 0 q
end ReciprocityTheory.MultiplicativeHeights
