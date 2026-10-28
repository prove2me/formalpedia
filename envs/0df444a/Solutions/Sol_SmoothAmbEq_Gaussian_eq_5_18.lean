-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.eq_5_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:52:07.52052+00:00
-- url     : https://prove2.me/submissions/bbdd5f52-7c69-4524-ae11-c08f004ed176

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SAEeq518

open SmoothAmbEq.Gaussian

lemma zeta_inv (M : Model) (t : ℝ) :
    (M.ζ t)⁻¹ = (M.σ ^ 2 + t * M.σ₀ ^ 2) / (M.σ ^ 2 * M.σ₀ ^ 2) := by
  unfold Model.ζ; rw [inv_div]

lemma den_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by
  have := M.hσ; have := M.hσ₀; positivity

lemma zeta_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.ζ t := by
  unfold Model.ζ
  have := den_pos M ht; have := M.hσ; have := M.hσ₀; positivity

lemma zeta_continuousOn (M : Model) : ContinuousOn M.ζ (Ici 0) := by
  unfold Model.ζ
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht; exact (den_pos M ht).ne'

/-- derivative of `(ζ t ^ 2)⁻¹`. -/
lemma hasDerivAt_zeta_inv_sq (M : Model) (t : ℝ) :
    HasDerivAt (fun t => (M.ζ t ^ 2)⁻¹)
      (2 * ((M.σ ^ 2 + t * M.σ₀ ^ 2) / (M.σ ^ 2 * M.σ₀ ^ 2)) * (M.σ₀ ^ 2 / (M.σ ^ 2 * M.σ₀ ^ 2)))
      t := by
  have e : (fun t => (M.ζ t ^ 2)⁻¹) =
      fun t => ((M.σ ^ 2 + t * M.σ₀ ^ 2) / (M.σ ^ 2 * M.σ₀ ^ 2)) ^ 2 := by
    funext t; rw [← zeta_inv, inv_pow]
  rw [e]
  have h1 : HasDerivAt (fun t => (M.σ ^ 2 + t * M.σ₀ ^ 2) / (M.σ ^ 2 * M.σ₀ ^ 2))
      (M.σ₀ ^ 2 / (M.σ ^ 2 * M.σ₀ ^ 2)) t := by
    have := ((hasDerivAt_id t).mul_const (M.σ₀ ^ 2)).const_add (M.σ ^ 2)
    simpa using this.div_const (M.σ ^ 2 * M.σ₀ ^ 2)
  exact (h1.pow 2).congr_deriv (by push_cast; ring)

/-- FTC for `t ↦ ∫_t^b f` within `[a, b]` for `f` continuous on `[a, b]`. -/
lemma ftc_left {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun u => ∫ s in u..b, f s) (-f t) (Icc a b) t := by
  set g : ℝ → ℝ := fun s => f (max a (min s b)) with hg_def
  have hgc : Continuous g := by
    apply hf.comp_continuous (by fun_prop)
    intro s; exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hgf : EqOn g f (Icc a b) := by
    intro s hs; simp [hg_def, min_eq_left hs.2, max_eq_right hs.1]
  have hd : HasDerivAt (fun u => ∫ s in u..b, g s) (-g t) t :=
    intervalIntegral.integral_hasDerivAt_left (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  rw [← hgf ht]
  refine hd.hasDerivWithinAt.congr_of_mem ?_ ht
  intro u hu
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hu.2] at hs
  exact (hgf ⟨hu.1.trans hs.1, hs.2⟩).symm

end SAEeq518

open SmoothAmbEq.Gaussian SAEeq518

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a) (hα : a < M.α)
    (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    SolvesODE510 M (coeffs518 M m₂ m₃) := by
  obtain ⟨hD, h2, h3, h2T, h3T⟩ := h
  have hT := M.hT
  have hσ := M.hσ
  have hσ2 : M.σ ^ 2 ≠ 0 := by positivity
  -- continuity of m₂, m₃ on [0, T]
  have c2 : ContinuousOn m₂ (Icc 0 M.T) := fun t ht => (h2 t ht).continuousWithinAt
  have c3 : ContinuousOn m₃ (Icc 0 M.T) := fun t ht => (h3 t ht).continuousWithinAt
  have cz : ContinuousOn M.ζ (Icc 0 M.T) :=
    (zeta_continuousOn M).mono (fun t ht => ht.1)
  have zpos : ∀ t ∈ Icc 0 M.T, 0 < M.ζ t := fun t ht => zeta_pos M ht.1
  have czi : ContinuousOn (fun t => (M.ζ t)⁻¹) (Icc 0 M.T) :=
    cz.inv₀ (fun t ht => (zpos t ht).ne')
  have cA1 : ContinuousOn (fun s => a₁ M s (m₂ s) (m₃ s)) (Icc 0 M.T) := by
    unfold a₁
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (hD t ht).ne'
  have cA2 : ContinuousOn (fun s => a₂ M s (m₂ s) (m₃ s)) (Icc 0 M.T) := by
    unfold a₂
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (hD t ht).ne'
  -- the key algebraic identity
  have key : ∀ t ∈ Icc 0 M.T, a₂ M t (m₂ t) (m₃ t) * (m₂ t + m₃ t)
      = a₁ M t (m₂ t) (m₃ t) - M.ζ t * m₂ t - 1 := by
    intro t ht
    have hd := (hD t ht).ne'
    have hz := (zpos t ht).ne'
    unfold a₁ a₂
    have hinv : ((M.ζ t)⁻¹ - M.α * m₃ t) * ((M.ζ t)⁻¹ - M.α * m₃ t)⁻¹ = 1 := mul_inv_cancel₀ hd
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(1 + M.ζ t * m₂ t)) * hinv
  -- m₁
  set F1 : ℝ → ℝ := fun t => ∫ s in t..M.T, M.ζ s ^ 2 * a₁ M s (m₂ s) (m₃ s) ^ 2 with hF1
  have dF1 : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt F1
      (-(M.ζ t ^ 2 * a₁ M t (m₂ t) (m₃ t) ^ 2)) (Icc 0 M.T) t := by
    intro t ht
    exact ftc_left hT.le (by fun_prop) ht
  set m₁ : ℝ → ℝ := fun t => (M.σ ^ 2)⁻¹ * (M.ζ t ^ 2)⁻¹ * F1 t with hm₁
  have d1 : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt m₁
      ((2 * M.ζ t * m₁ t - (a₁ M t (m₂ t) (m₃ t)) ^ 2) / M.σ ^ 2) (Icc 0 M.T) t := by
    intro t ht
    have hz := (zpos t ht).ne'
    have hd := (((hasDerivAt_zeta_inv_sq M t).hasDerivWithinAt (s := Icc 0 M.T)).const_mul
      (M.σ ^ 2)⁻¹).mul (dF1 t ht)
    refine (hd.congr_deriv ?_)
    have hzi := zeta_inv M t
    have hden := (den_pos M ht.1).ne'
    have hσ0 := M.hσ₀
    rw [hm₁]
    simp only
    rw [← hzi]
    field_simp
    ring
  have c1 : ContinuousOn m₁ (Icc 0 M.T) := fun t ht => (d1 t ht).continuousWithinAt
  -- m₅
  have d5 : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt (fun t => -M.r * m₂ t - M.r * m₃ t)
      (((1 + M.ζ t * m₂ t) * a₂ M t (m₂ t) (m₃ t) * (-M.r * m₂ t - M.r * m₃ t)
        - M.r * (1 + M.ζ t * m₂ t)) / M.σ ^ 2) (Icc 0 M.T) t := by
    intro t ht
    have hd := ((h2 t ht).const_mul (-M.r)).sub ((h3 t ht).const_mul M.r)
    refine (hd.congr_deriv ?_)
    have k := key t ht
    linear_combination (M.r * (1 + M.ζ t * m₂ t) / M.σ ^ 2) * k
  -- m₄
  have d4 : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt (fun t => -M.r * m₁ t - M.r * m₂ t)
      ((M.ζ t * (-M.r * m₁ t - M.r * m₂ t) - a₁ M t (m₂ t) (m₃ t) * a₂ M t (m₂ t) (m₃ t)
        * (-M.r * m₂ t - M.r * m₃ t) - M.r * M.ζ t * m₁ t) / M.σ ^ 2) (Icc 0 M.T) t := by
    intro t ht
    have hd := ((d1 t ht).const_mul (-M.r)).sub ((h2 t ht).const_mul M.r)
    refine (hd.congr_deriv ?_)
    have k := key t ht
    linear_combination (-(M.r * a₁ M t (m₂ t) (m₃ t)) / M.σ ^ 2) * k
  -- m₆
  have d6 : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt (coeffs518 M m₂ m₃).m₆
      ((-(1 / 2) * (a₂ M t (m₂ t) (m₃ t)) ^ 2 * (-M.r * m₂ t - M.r * m₃ t) ^ 2
        + 1 / 2 * M.r ^ 2 - 1 / 2 * M.ζ t ^ 2 * m₁ t
        - M.r * M.ζ t * (-M.r * m₁ t - M.r * m₂ t)) / M.σ ^ 2) (Icc 0 M.T) t := by
    intro t ht
    have hd := (ftc_left (f := fun s => 1 / 2 * a₂ M s (m₂ s) (m₃ s) ^ 2
        * (-M.r * m₂ s - M.r * m₃ s) ^ 2 - 1 / 2 * M.r ^ 2 + 1 / 2 * M.ζ s ^ 2 * m₁ s
        + M.r * M.ζ s * (-M.r * m₁ s - M.r * m₂ s)) hT.le (by fun_prop) ht).const_mul
        (M.σ ^ 2)⁻¹
    refine (hd.congr_deriv ?_)
    ring
  refine ⟨hD, d1, h2, h3, d4, d5, d6, ?_, h2T, h3T, ?_, ?_, ?_⟩
  · show m₁ M.T = 0
    simp [hm₁, hF1]
  · show -M.r * m₁ M.T - M.r * m₂ M.T = 0
    simp [hm₁, hF1, h2T]
  · show -M.r * m₂ M.T - M.r * m₃ M.T = 0
    simp [h2T, h3T]
  · show (M.σ ^ 2)⁻¹ * ∫ s in M.T..M.T, _ = 0
    simp
