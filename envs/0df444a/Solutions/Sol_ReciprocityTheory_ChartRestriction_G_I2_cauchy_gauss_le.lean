-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cauchy_gauss_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:28.140723+00:00
-- url     : https://prove2.me/submissions/05876c5a-917c-4a0d-a965-e13605632fdb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_iter_step_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {N k : ℕ} (F : (Fin N → ℂ) → ℂ) (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ z, ‖F z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S) (l : Fin k → Fin N) :
    ‖iteratedFDeriv ℂ k F 0 (fun j => Pi.single (l j) 1)‖ ≤
      Real.sqrt S * (Real.pi * Real.exp 1 * k) ^ ((k : ℝ) / 2) := by
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [iteratedFDeriv_zero_apply]
    have h0 := hS 0
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at h0
    simpa using Real.abs_le_sqrt h0
  · have hπk : 0 < Real.pi * k := by positivity
    obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = 1 / Real.sqrt (Real.pi * k) := ⟨_, rfl⟩
    have hρ : 0 < ρ := by rw [hρd]; positivity
    have hρ2 : ρ ^ 2 = 1 / (Real.pi * k) := by rw [hρd, div_pow, Real.sq_sqrt hπk.le, one_pow]
    have hbound := iter_step_bound F hF ρ (Real.sqrt S * Real.exp ((k : ℝ) / 2)) hρ k l 0 (by
      intro y hy
      simp only [Pi.zero_apply, sub_zero] at hy
      have hsq : ∑ i, ‖y i‖ ^ 2 ≤ k / Real.pi :=
        calc ∑ i, ‖y i‖ ^ 2 ≤ (∑ i, ‖y i‖) ^ 2 :=
              Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
          _ ≤ (k * ρ) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _) hy 2
          _ = k / Real.pi := by
              rw [mul_pow, hρ2]; field_simp
      have h2 : ‖F y‖ ^ 2 ≤ S * Real.exp k := by
        have he : ‖F y‖ ^ 2 = ‖F y‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖y i‖ ^ 2)
            * Real.exp (Real.pi * ∑ i, ‖y i‖ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]; simp
        rw [he]
        calc _ ≤ S * Real.exp (Real.pi * ∑ i, ‖y i‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (hS y) (Real.exp_pos _).le
          _ ≤ S * Real.exp k := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hS0
              calc Real.pi * ∑ i, ‖y i‖ ^ 2 ≤ Real.pi * (k / Real.pi) :=
                    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
                _ = k := by field_simp
      have hsx : Real.sqrt S * Real.exp ((k : ℝ) / 2) = Real.sqrt (S * Real.exp k) := by
        have : Real.exp (k : ℝ) = Real.exp ((k : ℝ) / 2) ^ 2 := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [Real.sqrt_mul hS0, this, Real.sqrt_sq (Real.exp_pos _).le]
      rw [hsx]
      simpa using Real.abs_le_sqrt h2)
    refine hbound.trans (le_of_eq ?_)
    have hr : ρ ^ k = 1 / (Real.pi * k) ^ ((k : ℝ) / 2) := by
      rw [hρd, div_pow, one_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hπk.le]
      ring_nf
    rw [show Real.pi * Real.exp 1 * k = (Real.pi * k) * Real.exp 1 by ring,
      Real.mul_rpow hπk.le (Real.exp_pos 1).le, Real.exp_one_rpow, hr]
    field_simp
end ReciprocityTheory.ChartRestriction.G.I2
