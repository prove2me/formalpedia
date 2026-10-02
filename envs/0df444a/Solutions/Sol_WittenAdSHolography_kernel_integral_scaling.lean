-- Prove2me | solution 1 for WittenAdSHolography.kernel_integral_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:37:23.090306+00:00
-- url     : https://prove2.me/submissions/85ad81b9-7373-4f2e-9222-6bc24a83527f

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology in
theorem solution (d : ℕ) (Δ : ℝ) (hΔ : (d : ℝ) / 2 < Δ) :
    Integrable (fun x : Bdry d => (1 + ‖x‖ ^ 2) ^ (-Δ)) ∧
      ∀ x₀ : ℝ, 0 < x₀ →
        ∫ x : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x‖ ^ 2) ^ Δ =
          ∫ x : Bdry d, (1 + ‖x‖ ^ 2) ^ (-Δ) := by
  have hfr : Module.finrank ℝ (Bdry d) = d := finrank_euclideanSpace_fin
  refine ⟨?_, ?_⟩
  · have h := integrable_rpow_neg_one_add_norm_sq (E := Bdry d) (μ := (volume : Measure (Bdry d)))
      (r := 2 * Δ) (by rw [hfr]; linarith)
    have he : -(2 * Δ) / 2 = -Δ := by ring
    rw [he] at h
    exact h
  · intro x₀ hx₀
    set f : Bdry d → ℝ := fun x => x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x‖ ^ 2) ^ Δ with hf
    have hsc := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Bdry d))) f x₀
    rw [hfr] at hsc
    have hpt : ∀ y : Bdry d, f (x₀ • y) = (x₀ ^ (d : ℝ))⁻¹ * (1 + ‖y‖ ^ 2) ^ (-Δ) := by
      intro y
      simp only [hf]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx₀]
      have h1 : x₀ ^ 2 + (x₀ * ‖y‖) ^ 2 = x₀ ^ 2 * (1 + ‖y‖ ^ 2) := by ring
      have hy : 0 < 1 + ‖y‖ ^ 2 := by positivity
      rw [h1, Real.mul_rpow (by positivity) hy.le]
      have h2 : (x₀ ^ 2 : ℝ) ^ Δ = x₀ ^ (2 * Δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]; norm_num
      rw [h2, Real.rpow_neg hy.le, Real.rpow_sub hx₀]
      have h3 : 0 < x₀ ^ (2 * Δ) := Real.rpow_pos_of_pos hx₀ _
      have h4 : 0 < x₀ ^ (d : ℝ) := Real.rpow_pos_of_pos hx₀ _
      have h5 : 0 < (1 + ‖y‖ ^ 2) ^ Δ := Real.rpow_pos_of_pos hy _
      field_simp
    simp_rw [hpt] at hsc
    rw [integral_const_mul] at hsc
    have h4 : 0 < x₀ ^ (d : ℝ) := Real.rpow_pos_of_pos hx₀ _
    have h6 : (x₀ ^ d : ℝ) = x₀ ^ (d : ℝ) := (Real.rpow_natCast x₀ d).symm
    rw [h6, abs_of_pos (inv_pos.mpr h4), smul_eq_mul] at hsc
    have := congrArg (fun t => x₀ ^ (d : ℝ) * t) hsc
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h4.ne', one_mul, one_mul] at this
    exact this.symm
