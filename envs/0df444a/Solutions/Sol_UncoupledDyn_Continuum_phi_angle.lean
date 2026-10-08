-- Prove2me | solution 1 for UncoupledDyn.Continuum.phi_angle
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:17:03.10708+00:00
-- url     : https://prove2.me/submissions/814bfca6-d65d-47b0-8e7f-011172486a9b

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting
open UncoupledDyn.Continuum
set_option maxHeartbeats 800000

private noncomputable def R : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
private noncomputable def c (z : ℂ) : ℂ :=
  let t := max ‖z‖ (1/3 : ℝ)
  (((1-t)/t : ℝ) : ℂ) + (((3*t-1)/(2*t) : ℝ) : ℂ) * R

private theorem phi_formula (z : ℂ) : phi z = c z * z := by
  unfold phi c
  split_ifs with h
  · rw [max_eq_right h]
    norm_num
  · rw [max_eq_left (le_of_not_ge h)]
    unfold R
    ring

private theorem rotation_norm : ‖R‖ = 1 := by
  simp [R, Complex.norm_exp]

private theorem rotation_parts : 0 < R.re ∧ 0 < R.im := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  simp only [R, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  constructor <;> linarith

private theorem coefficient_parts (z : ℂ) (hz : z ∈ D) :
    0 < (c z).re ∧ 0 ≤ (c z).im ∧ (1/3 < ‖z‖ → 0 < (c z).im) := by
  have hr : ‖z‖ ≤ 1 := by simpa [D, Metric.mem_closedBall, dist_zero_right] using hz
  have ht0 : 0 < max ‖z‖ (1/3 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ht1 : max ‖z‖ (1/3 : ℝ) ≤ 1 := max_le hr (by norm_num)
  have ha : 0 ≤ (1-max ‖z‖ (1/3 : ℝ))/max ‖z‖ (1/3 : ℝ) :=
    div_nonneg (by linarith) ht0.le
  have hb : 0 ≤ (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ)) :=
    div_nonneg (by linarith [le_max_right ‖z‖ (1/3 : ℝ)]) (by positivity)
  have hbreal : 0 < (c z).re := by
    by_cases hh : max ‖z‖ (1/3 : ℝ) = 1/3
    · dsimp only [c]
      rw [hh]
      norm_num
    · have hbp : 0 < (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ)) :=
        div_pos (by
          have ht : 1/3 < max ‖z‖ (1/3 : ℝ) :=
            lt_of_le_of_ne (le_max_right _ _) (Ne.symm hh)
          linarith) (by positivity)
      dsimp only [c]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact add_pos_of_nonneg_of_pos ha (mul_pos hbp rotation_parts.1)
  refine ⟨hbreal, ?_, ?_⟩
  · dsimp only [c]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add]
    exact mul_nonneg hb rotation_parts.2.le
  · intro hout
    have hbp : 0 < (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ)) :=
      div_pos (by linarith [le_max_left ‖z‖ (1/3 : ℝ)]) (by positivity)
    dsimp only [c]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add]
    exact mul_pos hbp rotation_parts.2


theorem UncoupledDyn.Continuum.phi_angle :
    ∀ z ∈ D, z ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      phi z = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * z := by
  intro z hz hne
  have hp := coefficient_parts z hz
  have hupper : (c z).im ≤ (c z).re := by
    have hr : ‖z‖ ≤ 1 := by simpa [D, Metric.mem_closedBall, dist_zero_right] using hz
    have ht : 0 < max ‖z‖ (1/3 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have ha : 0 ≤ (1-max ‖z‖ (1/3 : ℝ))/max ‖z‖ (1/3 : ℝ) :=
      div_nonneg (by linarith [max_le hr (show (1/3 : ℝ) ≤ 1 by norm_num)]) ht.le
    have he : R.re = R.im := by
      simp only [R, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
    dsimp only [c]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add, sub_zero]
    rw [he]
    linarith
  have hcne : c z ≠ 0 := by
    intro h
    have := hp.1
    simp [h] at this
  have harg0 : 0 ≤ (c z).arg := Complex.arg_nonneg_iff.mpr hp.2.1
  have harglt : (c z).arg < Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hp.1)
  have hearg : (c z).arg = Real.arctan ((c z).im / (c z).re) := by
    rw [← Complex.tan_arg]
    exact (Real.arctan_tan (by linarith [Real.pi_pos]) harglt).symm
  refine ⟨‖c z‖, norm_pos_iff.mpr hcne, (c z).arg, ⟨harg0, ?_⟩, ?_⟩
  · rw [hearg, ← Real.arctan_one]
    exact Real.arctan_le_arctan_iff.mpr ((div_le_one hp.1).mpr hupper)
  · rw [Complex.norm_mul_exp_arg_mul_I, phi_formula]

theorem solution :
    ∀ z ∈ D, z ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      phi z = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * z := UncoupledDyn.Continuum.phi_angle

#print axioms solution
