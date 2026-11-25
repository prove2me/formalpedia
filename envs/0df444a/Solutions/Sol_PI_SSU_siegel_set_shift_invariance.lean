-- Prove2me | solution 1 for PI.SSU.siegel_set_shift_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:24.294462+00:00
-- url     : https://prove2.me/submissions/ee9a831c-341c-49cd-86f4-4653a49ea7ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_SiegelSetShiftInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SSU
open Complex
namespace PI.SSU
theorem _root_.solution : ShiftInv := by
  intro f hf hper w n
  set g : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)) with hg
  have hgd : Differentiable ℂ g := by
    show Differentiable ℂ (fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)))
    exact hf.mul (by fun_prop)

  have hgp : ∀ z, g (z + 1) = g z := by
    intro z
    show f (z + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (z + 1))) =
      f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z))
    rw [hper z]
    congr 1
    rw [show -(2 * (Real.pi : ℂ) * I * n * (z + 1)) =
        -(2 * (Real.pi : ℂ) * I * n * z) + -((n : ℂ) * (2 * Real.pi * I)) by ring,
      Complex.exp_add, Complex.exp_neg ((n : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, inv_one, mul_one]

  have hvert : ∀ b : ℝ, ∫ x in (0 : ℝ)..1, g (x + b * I) = ∫ x in (0 : ℝ)..1, g x := by
    intro b
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0 (1 + b * I)
      hgd.differentiableOn
    have h1 : ((1 : ℂ) + b * I).re = 1 := by simp
    have h2 : ((1 : ℂ) + b * I).im = b := by simp
    rw [h1, h2, Complex.zero_re, Complex.zero_im] at hrect
    have hs : (fun y : ℝ => g (((1 : ℝ) : ℂ) + y * I)) = fun y : ℝ => g (((0 : ℝ) : ℂ) + y * I) := by
      funext y
      rw [← hgp (((0 : ℝ) : ℂ) + y * I)]
      congr 1
      push_cast
      ring
    rw [hs, add_sub_cancel_right, sub_eq_zero] at hrect
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hrect
    exact hrect.symm

  have hH : Function.Periodic (fun y : ℝ => g (y + w.im * I)) 1 := by
    intro y
    show g (((y + 1 : ℝ) : ℂ) + w.im * I) = g ((y : ℂ) + w.im * I)
    rw [← hgp ((y : ℂ) + w.im * I)]
    congr 1
    push_cast
    ring
  have hw : ∀ x : ℝ, (x : ℂ) + w = ((x + w.re : ℝ) : ℂ) + w.im * I := by
    intro x
    apply Complex.ext <;> simp
  calc ∫ x in (0 : ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))
      = ∫ x in (0 : ℝ)..1, (fun y : ℝ => g (y + w.im * I)) (x + w.re) := by
        congr 1
        funext x
        show g ((x : ℂ) + w) = g (((x + w.re : ℝ) : ℂ) + w.im * I)
        rw [hw x]
    _ = ∫ x in (0 + w.re)..(1 + w.re), (fun y : ℝ => g (y + w.im * I)) x :=
        intervalIntegral.integral_comp_add_right (fun y : ℝ => g (y + w.im * I)) w.re
    _ = ∫ x in (0 : ℝ)..(0 + 1), (fun y : ℝ => g (y + w.im * I)) x := by
        rw [zero_add w.re, add_comm 1 w.re]
        exact hH.intervalIntegral_add_eq w.re 0
    _ = ∫ x in (0 : ℝ)..1, g (x + w.im * I) := by rw [zero_add]
    _ = ∫ x in (0 : ℝ)..1, g x := hvert w.im
    _ = coef f n := rfl
end PI.SSU
