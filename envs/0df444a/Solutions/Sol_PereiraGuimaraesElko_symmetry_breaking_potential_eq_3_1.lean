-- Prove2me | solution 1 for PereiraGuimaraesElko.symmetry_breaking_potential_eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:15:24.448008+00:00
-- url     : https://prove2.me/submissions/92a6180f-afc4-4f06-a412-dcb8bf6bf719

import Mathlib

theorem solution (v₀ Λ σ V₀ μ α m : ℝ)
    (hv₀ : 0 ≤ v₀) (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hV₀ : V₀ = v₀ + Λ ^ 4) (hμ : μ = 2 * Λ ^ 2 / σ) (hα : α = 4 * Λ ^ 4 / σ ^ 4)
    (hm : m = Real.sqrt 2 * μ)
    (V : ℝ → ℝ) (hV : ∀ Φ, V Φ = v₀ + Λ ^ 4 * (1 - Φ ^ 2 / σ ^ 2) ^ 2) :
    (∀ Φ, V Φ = V₀ - 1 / 2 * μ ^ 2 * Φ ^ 2 + α / 4 * Φ ^ 4) ∧
      (∀ Φ, V σ ≤ V Φ) ∧ V σ = v₀ ∧
      deriv (deriv V) σ = m ^ 2 := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hVσ : V σ = v₀ := by rw [hV]; field_simp; ring
  have hVf : V = fun Φ => v₀ + Λ ^ 4 * (1 - Φ ^ 2 / σ ^ 2) ^ 2 := funext hV
  have hd1 : ∀ x, HasDerivAt V (Λ ^ 4 * (2 * (1 - x ^ 2 / σ ^ 2) * (-(2 * x) / σ ^ 2))) x := by
    intro x
    rw [hVf]
    have h1 : HasDerivAt (fun Φ : ℝ => 1 - Φ ^ 2 / σ ^ 2) (-(2 * x) / σ ^ 2) x := by
      have := ((hasDerivAt_pow 2 x).div_const (σ ^ 2)).const_sub 1
      refine this.congr_deriv ?_; field_simp; ring
    have h2 := (h1.pow 2).const_mul (Λ ^ 4) |>.const_add v₀
    refine h2.congr_deriv ?_; norm_num
  have hd1' : deriv V = fun x => Λ ^ 4 * (2 * (1 - x ^ 2 / σ ^ 2) * (-(2 * x) / σ ^ 2)) :=
    funext fun x => (hd1 x).deriv
  have hd2 : HasDerivAt (deriv V) (Λ ^ 4 * (-4 / σ ^ 2 + 12 * σ ^ 2 / σ ^ 4)) σ := by
    rw [hd1']
    have e : (fun x : ℝ => Λ ^ 4 * (2 * (1 - x ^ 2 / σ ^ 2) * (-(2 * x) / σ ^ 2))) =
        fun x => Λ ^ 4 * (-4 / σ ^ 2 * x + 4 / σ ^ 4 * x ^ 3) := by
      funext x; field_simp; ring
    rw [e]
    have := (((hasDerivAt_id σ).const_mul (-4 / σ ^ 2)).add
      ((hasDerivAt_pow 3 σ).const_mul (4 / σ ^ 4))).const_mul (Λ ^ 4)
    refine this.congr_deriv ?_; field_simp; ring
  refine ⟨fun Φ => ?_, fun Φ => ?_, hVσ, ?_⟩
  · rw [hV, hV₀, hμ, hα]; field_simp; ring
  · rw [hVσ, hV]; have := sq_nonneg (1 - Φ ^ 2 / σ ^ 2); have := pow_pos hΛ 4; nlinarith
  · rw [hd2.deriv, hm, hμ, mul_pow, Real.sq_sqrt (by norm_num)]
    field_simp; ring
