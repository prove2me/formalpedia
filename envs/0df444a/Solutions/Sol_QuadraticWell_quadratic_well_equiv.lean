-- Prove2me | solution 1 for QuadraticWell.quadratic_well_equiv
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-27T06:36:49.130836+00:00
-- url     : https://prove2.me/submissions/48769798-a5f9-4c56-b1ee-90e0ecbebb0e

import Mathlib

namespace QuadraticWellSol

theorem force_shift (a r₁ r₂ d : ℝ) (hr : r₁ ≠ r₂)
    (hd : d = (r₁ - r₂) / 2 ∨ d = (r₂ - r₁) / 2) (y : ℝ) :
    -a * (y - r₁) * (y - r₂) = -a * d ^ 2 * (((y - (r₁ + r₂) / 2) / d) ^ 2 - 1) := by
  have hd0 : d ≠ 0 := by
    rcases hd with rfl | rfl <;> intro h <;> apply hr <;> linarith
  field_simp
  rcases hd with rfl | rfl <;> ring

theorem sign_choice (a r₁ r₂ : ℝ) (ha : a ≠ 0) (hr : r₁ ≠ r₂) :
    0 < a * ((r₁ - r₂) / 2) ∨ 0 < a * ((r₂ - r₁) / 2) := by
  have h : a * ((r₁ - r₂) / 2) ≠ 0 := mul_ne_zero ha (by intro h; apply hr; linarith)
  rcases lt_or_gt_of_ne h with h | h
  · right; nlinarith
  · left; exact h

theorem rescale_deriv2 (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) (m d ω : ℝ) (hω : ω ≠ 0)
    (hd : d ≠ 0) (τ : ℝ) :
    deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ = deriv (deriv x) (τ / ω) / (ω ^ 2 * d) := by
  have h1 : Differentiable ℝ x := hx.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv x) := by
    have := (hx.iterate_deriv' 1 1).differentiable (by norm_num)
    simpa using this
  have hd1 : deriv (fun σ => (x (σ / ω) - m) / d) = fun σ => deriv x (σ / ω) * (1 / ω) / d := by
    funext σ
    have := (((h1 (σ / ω)).hasDerivAt.comp σ ((hasDerivAt_id σ).div_const ω)).sub_const m).div_const d
    simpa [Function.comp_def] using this.deriv
  rw [hd1]
  have := (((h2 (τ / ω)).hasDerivAt.comp τ ((hasDerivAt_id τ).div_const ω)).mul_const (1 / ω)).div_const d
  rw [show (fun σ => deriv x (σ / ω) * (1 / ω) / d) = fun σ => ((deriv x) ∘ (fun y => id y / ω)) σ * (1 / ω) / d from rfl,
    this.deriv]
  field_simp

/-- the core: any force of the right shape transforms to the normal form -/
theorem core (m d ω : ℝ) (hd : d ≠ 0) (hω : 0 < ω) (f : ℝ → ℝ)
    (hf : ∀ y, f y = -(ω ^ 2 * d) * (((y - m) / d) ^ 2 - 1)) (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) :
    ((∀ t, deriv (deriv x) t = f (x t)) ↔
     (∀ τ, deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ = -(((x (τ / ω) - m) / d) ^ 2 - 1))) := by
  have hω0 : ω ≠ 0 := hω.ne'
  simp only [rescale_deriv2 x hx m d ω hω0 hd]
  constructor
  · intro h τ
    rw [h, hf]; field_simp
  · intro h t
    have := h (ω * t)
    rw [show ω * t / ω = t by field_simp] at this
    rw [hf]
    field_simp at this ⊢
    linarith

theorem quadratic_well_equiv (a r₁ r₂ : ℝ) (ha : a ≠ 0) (hr : r₁ ≠ r₂) :
    ∃ m d ω : ℝ, d ≠ 0 ∧ 0 < ω ∧
      ∀ x : ℝ → ℝ, ContDiff ℝ 2 x →
        ((∀ t, deriv (deriv x) t = -a * (x t - r₁) * (x t - r₂)) ↔
         (∀ τ, deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ =
                -(((x (τ / ω) - m) / d) ^ 2 - 1))) := by
  have key : ∀ d, (d = (r₁ - r₂) / 2 ∨ d = (r₂ - r₁) / 2) → 0 < a * d → ∃ m d ω : ℝ, d ≠ 0 ∧ 0 < ω ∧
      ∀ x : ℝ → ℝ, ContDiff ℝ 2 x →
        ((∀ t, deriv (deriv x) t = -a * (x t - r₁) * (x t - r₂)) ↔
         (∀ τ, deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ =
                -(((x (τ / ω) - m) / d) ^ 2 - 1))) := by
    intro d hd had
    have hd0 : d ≠ 0 := by rintro rfl; simp at had
    refine ⟨(r₁ + r₂) / 2, d, Real.sqrt (a * d), hd0, Real.sqrt_pos.mpr had, fun x hx => ?_⟩
    apply core _ _ _ hd0 (Real.sqrt_pos.mpr had) (fun y => -a * (y - r₁) * (y - r₂)) _ x hx
    intro y
    rw [force_shift a r₁ r₂ d hr hd y, Real.sq_sqrt had.le]
    ring
  rcases sign_choice a r₁ r₂ ha hr with h | h
  · exact key _ (Or.inl rfl) h
  · exact key _ (Or.inr rfl) h

theorem golden_well (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) :
    (∀ t, deriv (deriv x) t = -(x t ^ 2 - x t - 1)) ↔
    (∀ τ, deriv (deriv (fun σ => (x (σ / Real.sqrt (Real.sqrt 5 / 2)) - 1 / 2) /
        (Real.sqrt 5 / 2))) τ =
      -(((x (τ / Real.sqrt (Real.sqrt 5 / 2)) - 1 / 2) / (Real.sqrt 5 / 2)) ^ 2 - 1)) := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h55 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 / 2 := by positivity
  apply core _ _ _ hpos.ne' (Real.sqrt_pos.mpr hpos) (fun y => -(y ^ 2 - y - 1)) _ x hx
  intro y
  rw [Real.sq_sqrt hpos.le]
  field_simp
  nlinarith [h55]

end QuadraticWellSol

theorem solution (a r₁ r₂ : ℝ) (ha : a ≠ 0) (hr : r₁ ≠ r₂) :
    ∃ m d ω : ℝ, d ≠ 0 ∧ 0 < ω ∧
      ∀ x : ℝ → ℝ, ContDiff ℝ 2 x →
        ((∀ t, deriv (deriv x) t = -a * (x t - r₁) * (x t - r₂)) ↔
         (∀ τ, deriv (deriv (fun σ => (x (σ / ω) - m) / d)) τ =
                -(((x (τ / ω) - m) / d) ^ 2 - 1))) := by
  apply QuadraticWellSol.quadratic_well_equiv <;> assumption
