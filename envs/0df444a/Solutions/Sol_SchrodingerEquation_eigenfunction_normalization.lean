-- Prove2me | solution 1 for SchrodingerEquation.eigenfunction_normalization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:11:12.949515+00:00
-- url     : https://prove2.me/submissions/fb9c1653-80eb-4860-ac2d-4b78199031ca

import Definitions.Def_SchrodingerEquation_infinite_well_model

open SchrodingerEquation

theorem solution (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, ‖eigenfunction L n x‖ ^ 2 = L / 2 := by
  have hc : (0 : ℝ) < n * Real.pi / L := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h1 : (fun x => ‖eigenfunction L n x‖ ^ 2) =
      fun x => Real.sin ((n * Real.pi / L) * x) ^ 2 := by
    funext x
    simp only [eigenfunction, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    congr 2; ring
  rw [h1, intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hc.ne', integral_sin_sq]
  have h2 : n * Real.pi / L * L = n * Real.pi := by field_simp
  rw [h2]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, Real.sin_nat_mul_pi]
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have hpi := Real.pi_ne_zero
  rw [smul_eq_mul]
  field_simp <;> ring
