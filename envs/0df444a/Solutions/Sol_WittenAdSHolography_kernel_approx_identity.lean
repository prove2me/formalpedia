-- Prove2me | solution 1 for WittenAdSHolography.kernel_approx_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:22:56.885628+00:00
-- url     : https://prove2.me/submissions/86fcc77e-a3d9-40fc-ab7c-395ee784fce8

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology in
theorem c0324c3d_rescale (d : ℕ) (Δ : ℝ) (φ₀ : Bdry d → ℝ) (x : Bdry d) (x₀ : ℝ) (hx₀ : 0 < x₀) :
    ∫ x' : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x - x'‖ ^ 2) ^ Δ * φ₀ x' =
      ∫ u : Bdry d, (1 + ‖u‖ ^ 2) ^ (-Δ) * φ₀ (x - x₀ • u) := by
  have hfr : Module.finrank ℝ (Bdry d) = d := finrank_euclideanSpace_fin
  set h : Bdry d → ℝ := fun y => x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖y‖ ^ 2) ^ Δ * φ₀ (x - y) with hh
  have e1 : (∫ x' : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x - x'‖ ^ 2) ^ Δ * φ₀ x') =
      ∫ x' : Bdry d, h (x - x') := by
    congr 1; funext x'; simp only [hh, sub_sub_cancel]
  rw [e1, integral_sub_left_eq_self h (volume : Measure (Bdry d)) x]
  have hsc := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Bdry d))) h x₀
  rw [hfr] at hsc
  have hpt : ∀ y : Bdry d, h (x₀ • y) =
      (x₀ ^ (d : ℝ))⁻¹ * ((1 + ‖y‖ ^ 2) ^ (-Δ) * φ₀ (x - x₀ • y)) := by
    intro y
    simp only [hh]
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

open WittenAdSHolography MeasureTheory Filter Topology in
theorem solution (d : ℕ) (Δ : ℝ) (hΔ : (d : ℝ) / 2 < Δ) (φ₀ : Bdry d → ℝ)
    (hcont : Continuous φ₀) (hbdd : ∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) (x : Bdry d) :
    Tendsto
      (fun x₀ : ℝ => ∫ x' : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x - x'‖ ^ 2) ^ Δ * φ₀ x')
      (𝓝[>] 0) (𝓝 ((∫ u : Bdry d, (1 + ‖u‖ ^ 2) ^ (-Δ)) * φ₀ x)) := by
  obtain ⟨B, hB⟩ := hbdd
  have hfr : Module.finrank ℝ (Bdry d) = d := finrank_euclideanSpace_fin
  have hint : Integrable (fun u : Bdry d => (1 + ‖u‖ ^ 2) ^ (-Δ)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := Bdry d) (μ := (volume : Measure (Bdry d)))
      (r := 2 * Δ) (by rw [hfr]; linarith)
    have he : -(2 * Δ) / 2 = -Δ := by ring
    rw [he] at h
    exact h
  have hcongr : (fun x₀ : ℝ => ∫ u : Bdry d, (1 + ‖u‖ ^ 2) ^ (-Δ) * φ₀ (x - x₀ • u))
      =ᶠ[𝓝[>] 0]
      (fun x₀ : ℝ => ∫ x' : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x - x'‖ ^ 2) ^ Δ * φ₀ x') := by
    filter_upwards [self_mem_nhdsWithin] with x₀ hx₀
    exact (c0324c3d_rescale d Δ φ₀ x x₀ hx₀).symm
  refine Tendsto.congr' hcongr ?_
  rw [← integral_mul_const]
  have hmeas : ∀ x₀ : ℝ, Continuous (fun u : Bdry d => (1 + ‖u‖ ^ 2) ^ (-Δ) * φ₀ (x - x₀ • u)) := by
    intro x₀
    refine Continuous.mul ?_ ?_
    · exact Continuous.rpow_const (by fun_prop) (fun u => Or.inl (by positivity))
    · exact hcont.comp (by fun_prop)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : Bdry d => B * (1 + ‖u‖ ^ 2) ^ (-Δ)) ?_ ?_ (hint.const_mul B) ?_
  · exact Eventually.of_forall (fun x₀ => (hmeas x₀).aestronglyMeasurable)
  · refine Eventually.of_forall (fun x₀ => Eventually.of_forall (fun u => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have hp : 0 ≤ (1 + ‖u‖ ^ 2) ^ (-Δ) := Real.rpow_nonneg (by positivity) _
    rw [abs_of_nonneg hp, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _) hp
  · refine Eventually.of_forall (fun u => ?_)
    apply Tendsto.const_mul
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun x₀ : ℝ => φ₀ (x - x₀ • u)) := hcont.comp (by fun_prop)
    have := hc.tendsto 0
    simpa using this
