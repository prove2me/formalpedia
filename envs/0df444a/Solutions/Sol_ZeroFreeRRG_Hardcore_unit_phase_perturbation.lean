-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.unit_phase_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.648572+00:00
-- url     : https://prove2.me/submissions/8b85a468-b02e-4caa-b663-dd688c389675

import Mathlib
set_option autoImplicit false

theorem solution (u v : ℂ) (r : ℝ) (hu : ‖u‖ = 1)
    (hr0 : 0 ≤ r) (hr : r ≤ 96/625) (hclose : ‖u-v‖ ≤ r) :
    v ≠ 0 ∧ ‖u-v/(‖v‖:ℂ)‖ ≤ (25/23)*r := by
  have hvn : 1-r ≤ ‖v‖ := by
    have hh := norm_sub_norm_le u v
    rw [hu] at hh
    linarith
  have hvpos : 0 < ‖v‖ := by linarith
  have hv : v ≠ 0 := norm_pos_iff.mp hvpos
  have hnco : (‖v‖:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hvpos
  let w := v/(‖v‖:ℂ)
  have hw : ‖w‖=1 := by
    dsimp [w]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hvpos,div_self (ne_of_gt hvpos)]
  have hvw : v = w*(‖v‖:ℂ) := by dsimp [w]; field_simp
  have hgeom1 := Complex.normSq_sub u v
  have hgeom2 := Complex.normSq_sub u w
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,hu] at hgeom1
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,hu,hw] at hgeom2
  have hcross : (u * (starRingEnd ℂ) v).re = ‖v‖*(u * (starRingEnd ℂ) w).re := by
    conv_lhs => rw [hvw]
    simp [map_mul,Complex.mul_re]
    ring
  rw [hcross] at hgeom1
  have hprod : ‖v‖ * ‖u-w‖^2 ≤ ‖u-v‖^2 := by
    nlinarith [sq_nonneg (‖v‖-1)]
  have hb : (23/25:ℝ)^2 ≤ ‖v‖ := by linarith
  have he : ‖u-v‖^2 ≤ r^2 := by nlinarith [norm_nonneg (u-v)]
  have hp : (23/25:ℝ)^2 * ‖u-w‖^2 ≤ ‖v‖ * ‖u-w‖^2 :=
    mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hc : ((23/25:ℝ)*‖u-w‖)^2 ≤ r^2 := by nlinarith [hp,hprod,he]
  have hfinal : ‖u-w‖ ≤ (25/23)*r := by nlinarith [norm_nonneg (u-w)]
  exact ⟨hv,hfinal⟩
