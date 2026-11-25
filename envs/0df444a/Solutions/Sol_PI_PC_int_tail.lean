-- Prove2me | solution 1 for PI.PC.int_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:31.960498+00:00
-- url     : https://prove2.me/submissions/4a1afe71-4dd6-4aa7-89b0-e576f28123a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_phi_intervalIntegrable
import Theorems.Thm_PI_PC_gg_hasDerivAt
import Theorems.Thm_PI_PC_chebyshevPrimeBounds_log_fact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution (hU : CHUpper) {x : ℝ} (hx : 1024 ≤ x) :
    ∫ t in (1024 : ℝ)..x, phi t ≤ gg x - gg 1024 := by
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hpt : ∀ t ∈ Icc (1024 : ℝ) x, phi t ≤ gg' t := by
    intro t ht
    have ht1 : (1024 : ℝ) ≤ t := ht.1
    have ht0 : 0 < t := by linarith
    have ht0' : t ≠ 0 := ht0.ne'
    have hL : 10 * log 2 ≤ log t := by
      rw [← chebyshevPrimeBounds_log_fact]; exact Real.log_le_log (by norm_num) ht1
    have hLpos : 0 < log t := by linarith
    have hL0 : log t ≠ 0 := hLpos.ne'
    have hψ := hU t (by linarith)
    have hθ := Chebyshev.theta_le_psi t
    unfold phi gg'
    rw [div_le_iff₀ (mul_pos ht0 (pow_pos hLpos 2))]
    have e : (1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t) * (t * log t ^ 2) =
        1.56 * t - 1.56 * 2 * t / log t + 0.7 * log t ^ 2 := by
      first | (field_simp; ring) | field_simp
    rw [e]
    have h3 : 1.56 * 2 * t / log t ≤ 0.4544 * t := by
      rw [div_le_iff₀ hLpos]
      nlinarith [mul_le_mul_of_nonneg_left hL ht0.le, mul_lt_mul_of_pos_left hl2 ht0]
    linarith
  have hderiv : ∀ t ∈ uIcc (1024 : ℝ) x, HasDerivAt gg (gg' t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact gg_hasDerivAt (by linarith [ht.1])
  have hcont : ContinuousOn gg' (uIcc 1024 x) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hl2' : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    have hl3 : log t ^ 3 ≠ 0 := pow_ne_zero 3 hl
    apply ContinuousAt.continuousWithinAt
    show ContinuousAt (fun s : ℝ => 1.56 * (1 / log s ^ 2 - 2 / log s ^ 3) + 0.7 / s) t
    fun_prop (disch := assumption)
  have hint_r : IntervalIntegrable gg' volume 1024 x := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_r
  have hmono : ∫ t in (1024 : ℝ)..x, phi t ≤ ∫ t in (1024 : ℝ)..x, gg' t :=
    intervalIntegral.integral_mono_on hx (phi_intervalIntegrable (by norm_num) hx) hint_r hpt
  exact hmono.trans_eq hftc
end PI.PC
