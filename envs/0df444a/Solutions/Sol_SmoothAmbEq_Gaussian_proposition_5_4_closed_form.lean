-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.proposition_5_4_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:20:56.891237+00:00
-- url     : https://prove2.me/submissions/ccdfa752-1682-4aa6-b7df-73f9447771cc

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SAECF

open SmoothAmbEq.Gaussian

lemma den_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by
  have := M.hσ; have := M.hσ₀; positivity

lemma zeta_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.ζ t := by
  unfold Model.ζ
  have := den_pos M ht; have := M.hσ; have := M.hσ₀; positivity

lemma hasDerivAt_zeta (M : Model) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt M.ζ (-(M.ζ t ^ 2) / M.σ ^ 2) t := by
  have hd := den_pos M ht
  have e : M.ζ = fun t => M.σ ^ 2 * M.σ₀ ^ 2 * (M.σ ^ 2 + t * M.σ₀ ^ 2)⁻¹ := by
    funext t; unfold Model.ζ; rw [div_eq_mul_inv]
  have h := (((hasDerivAt_id t).mul_const (M.σ₀ ^ 2)).const_add (M.σ ^ 2)).inv hd.ne'
  rw [e]
  refine (h.const_mul (M.σ ^ 2 * M.σ₀ ^ 2)).congr_deriv ?_
  have := M.hσ
  simp only [id]
  field_simp

/-- A function with `|p'| ≤ C|p|` on `[0, T]` and `p(T) > 0` stays positive on `[0, T]`. -/
lemma barrier {p q : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt p (q t) (Icc 0 T) t)
    (hq : ∀ t ∈ Icc 0 T, |q t| ≤ C * |p t|) (hpT : 0 < p T) :
    ∀ t ∈ Icc 0 T, 0 < p t := by
  have hc : ContinuousOn p (Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  intro t ht
  by_contra hneg
  push Not at hneg
  -- a zero of `p` in `[t, T]`
  obtain ⟨t₁, ht₁, hp₁⟩ : ∃ t₁ ∈ Icc t T, p t₁ = 0 := by
    have := intermediate_value_Icc ht.2 (hc.mono (Icc_subset_Icc_left ht.1))
    exact this ⟨hneg, hpT.le⟩
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := p) (f' := q) (K := C)
    (hc.mono (Icc_subset_Icc_left (ht.1.trans ht₁.1)))
    (fun x hx => (hd x ⟨ht.1.trans (ht₁.1.trans hx.1), hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2)
        (Icc_subset_Icc_left (ht.1.trans (ht₁.1.trans hx.1)))))
    hp₁
    (fun x hx => by
      simpa [Real.norm_eq_abs] using hq x ⟨ht.1.trans (ht₁.1.trans hx.1), hx.2.le⟩)
  have := hz T ⟨ht₁.2, le_rfl⟩
  linarith


lemma eq_of_deriv_zero {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f 0 (Icc 0 T) t) : ∀ t ∈ Icc 0 T, f t = f T := by
  have hc : ContinuousOn f (Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  have := constant_of_has_deriv_right_zero hc (fun x hx =>
    (hd x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)))
  intro t ht
  rw [this t ht, this T ⟨hT, le_rfl⟩]

lemma core (M : Model) (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    (∀ t ∈ Icc 0 M.T, HasDerivWithinAt (fun t => M.ζ t * m₂ t)
      ((1 + M.ζ t * m₂ t) ^ 2 * (1 + M.α * (M.ζ t * m₂ t)) /
        (M.σ ^ 2 * ((M.ζ t)⁻¹ - M.α * m₃ t))) (Icc 0 M.T) t) ∧
    (∀ t ∈ Icc 0 M.T, 0 < 1 + M.ζ t * m₂ t) ∧
    (∀ t ∈ Icc 0 M.T, 0 < 1 + M.α * (M.ζ t * m₂ t)) ∧
    (∀ t ∈ Ico 0 M.T, M.ζ t * m₂ t < 0) := by
  obtain ⟨hD, h2, h3, h2T, h3T⟩ := h
  have hT := M.hT
  have hσ := M.hσ
  have hσ2 : 0 < M.σ ^ 2 := by positivity
  set α := M.α with hαdef
  set D : ℝ → ℝ := fun t => (M.ζ t)⁻¹ - α * m₃ t with hDdef
  set u : ℝ → ℝ := fun t => M.ζ t * m₂ t with hudef
  have zpos : ∀ t ∈ Icc 0 M.T, 0 < M.ζ t := fun t ht => zeta_pos M ht.1
  -- derivative of `u = ζ m₂`
  have hu : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt u
      ((1 + u t) ^ 2 * (1 + α * u t) / (M.σ ^ 2 * D t)) (Icc 0 M.T) t := by
    intro t ht
    have hz := ((hasDerivAt_zeta M ht.1).hasDerivWithinAt (s := Icc 0 M.T)).mul (h2 t ht)
    refine hz.congr_deriv ?_
    have hz0 := (zpos t ht).ne'
    have hD0 := (hD t ht).ne'
    simp only [hudef, hDdef, a₁]
    set w := (M.ζ t)⁻¹ with hw
    have hzw : M.ζ t * w = 1 := mul_inv_cancel₀ hz0
    rw [← div_div]
    linear_combination ((M.σ ^ 2)⁻¹ * (w - α * m₃ t)⁻¹ * (1 + M.ζ t * m₂ t) ^ 2) * hzw
  have cu : ContinuousOn u (Icc 0 M.T) := fun t ht => (hu t ht).continuousWithinAt
  have c3 : ContinuousOn m₃ (Icc 0 M.T) := fun t ht => (h3 t ht).continuousWithinAt
  have cD : ContinuousOn D (Icc 0 M.T) := fun t ht => by
    have hz := (hasDerivAt_zeta M ht.1).continuousAt.continuousWithinAt (s := Icc 0 M.T)
    exact (hz.inv₀ (zpos t ht).ne').sub ((c3 t ht).const_smul α)
  -- uniform bounds on `[0, T]`
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn cu
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 hT.le) cD
  set d₀ := D t₀ with hd₀
  have hd₀pos : 0 < d₀ := hD t₀ ht₀
  have hDge : ∀ t ∈ Icc 0 M.T, d₀ ≤ D t := fun t ht => hmin ht
  have hUabs : ∀ t ∈ Icc 0 M.T, |u t| ≤ U := fun t ht => by
    simpa [Real.norm_eq_abs] using hU t ht
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hUabs 0 ⟨le_rfl, hT.le⟩)
  have hinvD : ∀ t ∈ Icc 0 M.T, 1 / (M.σ ^ 2 * D t) ≤ 1 / (M.σ ^ 2 * d₀) := fun t ht => by
    gcongr; exact hDge t ht
  -- positivity of `1 + u`
  have hp1 : ∀ t ∈ Icc 0 M.T, 0 < 1 + u t := by
    refine barrier (p := fun t => 1 + u t)
      (q := fun t => (1 + u t) ^ 2 * (1 + α * u t) / (M.σ ^ 2 * D t))
      (C := (1 + U) * (1 + |α| * U) / (M.σ ^ 2 * d₀)) hT.le
      (fun t ht => (hu t ht).const_add 1) ?_ (by simp [hudef, h2T])
    intro t ht
    have hDt : 0 < M.σ ^ 2 * D t := mul_pos hσ2 (hD t ht)
    have hut := hUabs t ht
    have e : |(1 + u t) ^ 2 * (1 + α * u t) / (M.σ ^ 2 * D t)|
        = |1 + u t| * (|1 + u t| * |1 + α * u t|) * (1 / (M.σ ^ 2 * D t)) := by
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hDt, sq]; ring
    rw [e]
    have b1 : |1 + u t| ≤ 1 + U := (abs_add_le _ _).trans (by simp [hut])
    have b2 : |1 + α * u t| ≤ 1 + |α| * U :=
      (abs_add_le _ _).trans (by
        rw [abs_one, abs_mul]; gcongr)
    have b3 := hinvD t ht
    calc |1 + u t| * (|1 + u t| * |1 + α * u t|) * (1 / (M.σ ^ 2 * D t))
        ≤ |1 + u t| * ((1 + U) * (1 + |α| * U)) * (1 / (M.σ ^ 2 * d₀)) := by
          gcongr
      _ = (1 + U) * (1 + |α| * U) / (M.σ ^ 2 * d₀) * |1 + u t| := by ring
  -- positivity of `1 + α u`
  have hp2 : ∀ t ∈ Icc 0 M.T, 0 < 1 + α * u t := by
    refine barrier (p := fun t => 1 + α * u t)
      (q := fun t => α * ((1 + u t) ^ 2 * (1 + α * u t) / (M.σ ^ 2 * D t)))
      (C := |α| * (1 + U) ^ 2 / (M.σ ^ 2 * d₀)) hT.le
      (fun t ht => ((hu t ht).const_mul α).const_add 1) ?_ (by simp [hudef, h2T])
    intro t ht
    have hDt : 0 < M.σ ^ 2 * D t := mul_pos hσ2 (hD t ht)
    have hut := hUabs t ht
    have e : |α * ((1 + u t) ^ 2 * (1 + α * u t) / (M.σ ^ 2 * D t))|
        = |α| * |1 + u t| ^ 2 * (1 / (M.σ ^ 2 * D t)) * |1 + α * u t| := by
      rw [abs_mul, abs_div, abs_mul, abs_pow, abs_of_pos hDt]; ring
    rw [e]
    have b1 : |1 + u t| ≤ 1 + U := (abs_add_le _ _).trans (by simp [hut])
    have b3 := hinvD t ht
    calc |α| * |1 + u t| ^ 2 * (1 / (M.σ ^ 2 * D t)) * |1 + α * u t|
        ≤ |α| * (1 + U) ^ 2 * (1 / (M.σ ^ 2 * d₀)) * |1 + α * u t| := by gcongr
      _ = |α| * (1 + U) ^ 2 / (M.σ ^ 2 * d₀) * |1 + α * u t| := by ring
  -- `u` is strictly increasing on `[0, T]`
  have hupos : ∀ t ∈ Icc 0 M.T, 0 < (1 + u t) ^ 2 * (1 + α * u t) / (M.σ ^ 2 * D t) :=
    fun t ht => by
      have := hp1 t ht; have := hp2 t ht; have := hD t ht
      positivity
  have hmono : StrictMonoOn u (Icc 0 M.T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 M.T) cu
    intro t ht
    rw [interior_Icc] at ht
    have hd := (hu t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [hd.deriv]
    exact hupos t (Ioo_subset_Icc_self ht)
  have hulT : ∀ t ∈ Ico 0 M.T, u t < 0 := fun t ht => by
    have := hmono ⟨ht.1, ht.2.le⟩ ⟨hT.le, le_rfl⟩ ht.2
    simpa [hudef, h2T] using this
  exact ⟨hu, hp1, hp2, hulT⟩

end SAECF

open SmoothAmbEq.Gaussian SAECF

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    (M.α = 0 → ∀ t ∈ Icc 0 M.T,
      m₂ t = (M.ζ t)⁻¹ / (1 + Real.log (M.ζ t / M.ζ M.T)) - (M.ζ t)⁻¹ ∧
      m₃ t = (M.ζ M.T)⁻¹ * (∫ x in (0 : ℝ)..Real.log (M.ζ t / M.ζ M.T),
          Real.exp (-x) * ((1 + x) ^ 2)⁻¹) - (M.T - t) / M.σ ^ 2) ∧
    (M.α = 1 → ∀ t ∈ Icc 0 M.T,
      m₂ t = (M.ζ t)⁻¹ / (1 + (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t)) - (M.ζ t)⁻¹ ∧
      m₃ t = (M.ζ t)⁻¹ - (M.ζ M.T)⁻¹ / (1 + (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t))) ∧
    (M.α ≠ 0 → M.α ≠ 1 → ∀ t ∈ Icc 0 M.T,
      -(M.ζ t * m₂ t) ∈ Ico 0 (1 / max M.α 1) ∧
      Ψ M (-(M.ζ t * m₂ t)) = (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t) ∧
      m₃ t = 1 / M.α * ((M.ζ t)⁻¹ - (M.ζ M.T)⁻¹
        * Real.exp (M.ζ t * m₂ t / (1 + M.ζ t * m₂ t))
        * (1 + M.ζ t * m₂ t) ^ (M.α / (M.α - 1))
        * (1 + M.α * M.ζ t * m₂ t) ^ (-1 / (M.α - 1)))) := by
  obtain ⟨hu, hp1, hp2, hneg⟩ := core M m₂ m₃ h
  obtain ⟨hD, h2, h3, h2T, h3T⟩ := h
  have hT := M.hT
  have hσ := M.hσ
  have hσ2 : 0 < M.σ ^ 2 := by positivity
  have zpos : ∀ t ∈ Icc 0 M.T, 0 < M.ζ t := fun t ht => zeta_pos M ht.1
  have hTmem : M.T ∈ Icc 0 M.T := ⟨hT.le, le_rfl⟩
  have zT := zpos M.T hTmem
  have huT : M.ζ M.T * m₂ M.T = 0 := by simp [h2T]
  have hDT : (M.ζ M.T)⁻¹ - M.α * m₃ M.T = (M.ζ M.T)⁻¹ := by simp [h3T]
  have hDd : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt (fun t => (M.ζ t)⁻¹ - M.α * m₃ t)
      ((1 + 2 * M.α * (M.ζ t * m₂ t) + M.α * (M.ζ t * m₂ t) ^ 2) / M.σ ^ 2) (Icc 0 M.T) t := by
    intro t ht
    have hz0 := (zpos t ht).ne'
    have := (((hasDerivAt_zeta M ht.1).inv hz0).hasDerivWithinAt (s := Icc 0 M.T)).sub
      ((h3 t ht).const_mul M.α)
    refine this.congr_deriv ?_
    field_simp
    ring
  -- `1 / (1 + u)` and its derivative
  have hinvu : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt (fun s => 1 / (1 + (M.ζ s * m₂ s)))
      (-((1 + (M.ζ t * m₂ t)) ^ 2 * (1 + M.α * (M.ζ t * m₂ t)) / (M.σ ^ 2 * ((M.ζ t)⁻¹ - M.α * m₃ t))) / (1 + (M.ζ t * m₂ t)) ^ 2) (Icc 0 M.T) t := by
    intro t ht
    have := ((hu t ht).const_add 1).inv (hp1 t ht).ne'
    simp only [one_div]
    exact this
  refine ⟨fun hα0 => ?_, fun hα1 => ?_, fun hα0 hα1 => ?_⟩
  · ------------------------------------------------------------------ case α = 0
    have hDz : ∀ t, ((M.ζ t)⁻¹ - M.α * m₃ t) = (M.ζ t)⁻¹ := fun t => by simp [hα0]
    -- `1/(1+u) - log ζ` is constant
    have hg := eq_of_deriv_zero (f := fun s => 1 / (1 + (M.ζ s * m₂ s)) - Real.log (M.ζ s)) hT.le
      (fun t ht => by
        have hz0 := (zpos t ht).ne'
        have h1 := hinvu t ht
        have h2' := ((hasDerivAt_zeta M ht.1).log hz0).hasDerivWithinAt (s := Icc 0 M.T)
        refine (h1.sub h2').congr_deriv ?_
        rw [hDz t, hα0]
        have := (hp1 t ht).ne'
        field_simp
        ring)
    -- the formula for `1 + log(ζ t / ζ T)`
    have hL : ∀ t ∈ Icc 0 M.T, 1 + Real.log (M.ζ t / M.ζ M.T) = 1 / (1 + (M.ζ t * m₂ t)) := by
      intro t ht
      have := hg t ht
      simp only [huT, add_zero, div_one] at this
      rw [Real.log_div (zpos t ht).ne' zT.ne']
      linarith
    -- `m₃`
    set I : ℝ → ℝ := fun y => ∫ x in (0 : ℝ)..y, Real.exp (-x) * ((1 + x) ^ 2)⁻¹ with hIdef
    have fcont : ContinuousOn (fun x : ℝ => Real.exp (-x) * ((1 + x) ^ 2)⁻¹) (Ioi (-1)) := by
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.inv₀ (by fun_prop)
      intro x hx
      have : 0 < 1 + x := by have : -1 < x := hx; linarith
      positivity
    have hI : ∀ y, -1 < y → HasDerivAt I (Real.exp (-y) * ((1 + y) ^ 2)⁻¹) y := by
      intro y hy
      apply intervalIntegral.integral_hasDerivAt_right
      · apply ContinuousOn.intervalIntegrable
        apply fcont.mono
        intro x hx
        rcases le_total 0 y with h0 | h0
        · rw [uIcc_of_le h0] at hx; show -1 < x; linarith [hx.1]
        · rw [uIcc_of_ge h0] at hx; show -1 < x; linarith [hx.1]
      · exact fcont.stronglyMeasurableAtFilter isOpen_Ioi y hy
      · exact fcont.continuousAt (isOpen_Ioi.mem_nhds hy)
    set L : ℝ → ℝ := fun s => Real.log (M.ζ s / M.ζ M.T) with hLdef
    have hLd : ∀ t ∈ Icc 0 M.T, HasDerivWithinAt L (-(M.ζ t) / M.σ ^ 2) (Icc 0 M.T) t := by
      intro t ht
      have hz0 := (zpos t ht).ne'
      have := (((hasDerivAt_zeta M ht.1).div_const (M.ζ M.T)).log
        (div_ne_zero hz0 zT.ne')).hasDerivWithinAt (s := Icc 0 M.T)
      refine this.congr_deriv ?_
      field_simp
    have hLgt : ∀ t ∈ Icc 0 M.T, -1 < L t := by
      intro t ht
      have := hL t ht
      have hp := hp1 t ht
      have : 0 < 1 + L t := by simp only [hLdef]; rw [this]; positivity
      linarith
    have hm3 := eq_of_deriv_zero
      (f := fun s => m₃ s - ((M.ζ M.T)⁻¹ * I (L s) - (M.T - s) / M.σ ^ 2)) hT.le
      (fun t ht => by
        have hz0 := (zpos t ht).ne'
        have hcomp := (hI (L t) (hLgt t ht)).comp_hasDerivWithinAt t (hLd t ht)
        have hlin : HasDerivWithinAt (fun s => (M.T - s) / M.σ ^ 2) (-1 / M.σ ^ 2)
            (Icc 0 M.T) t :=
          (((hasDerivAt_id t).const_sub M.T).div_const (M.σ ^ 2)).hasDerivWithinAt
        refine ((h3 t ht).sub ((hcomp.const_mul (M.ζ M.T)⁻¹).sub hlin)).congr_deriv ?_
        have hexp : Real.exp (-L t) = M.ζ M.T / M.ζ t := by
          rw [Real.exp_neg, hLdef]
          simp only
          rw [Real.exp_log (div_pos (zpos t ht) zT), inv_div]
        have h1L := hL t ht
        simp only [hLdef] at hexp
        simp only [Function.comp_def, hLdef, hexp, h1L]
        have := (hp1 t ht).ne'
        field_simp
        ring)
    intro t ht
    refine ⟨?_, ?_⟩
    · have h1L := hL t ht
      rw [h1L]
      have := (hp1 t ht).ne'
      have hz0 := (zpos t ht).ne'
      field_simp
      ring
    · have := hm3 t ht
      simp only [h3T, hLdef, div_self zT.ne', Real.log_one, hIdef, intervalIntegral.integral_same,
        mul_zero, sub_self, zero_div, sub_zero] at this
      linarith
  · ------------------------------------------------------------------ case α = 1
    -- `D / (1 + u)` is constant
    have hq := eq_of_deriv_zero (f := fun s => ((M.ζ s)⁻¹ - M.α * m₃ s) / (1 + (M.ζ s * m₂ s))) hT.le
      (fun t ht => by
        have hp := (hp1 t ht).ne'
        have hDt := (hD t ht).ne'
        refine ((hDd t ht).div ((hu t ht).const_add 1) hp).congr_deriv ?_
        generalize (M.ζ t)⁻¹ - M.α * m₃ t = Dv at hDt ⊢
        generalize M.ζ t * m₂ t = U at hp ⊢
        rw [hα1]
        field_simp
        ring)
    have hDu : ∀ t ∈ Icc 0 M.T, ((M.ζ t)⁻¹ - M.α * m₃ t) = (M.ζ M.T)⁻¹ * (1 + (M.ζ t * m₂ t)) := by
      intro t ht
      have := hq t ht
      simp only [huT, hDT, add_zero, div_one] at this
      have hp := (hp1 t ht).ne'
      rw [div_eq_iff hp] at this
      linarith
    have hr := eq_of_deriv_zero
      (f := fun s => 1 / (1 + (M.ζ s * m₂ s)) + M.ζ M.T * s / M.σ ^ 2) hT.le
      (fun t ht => by
        have hp := (hp1 t ht).ne'
        have hlin : HasDerivWithinAt (fun s => M.ζ M.T * s / M.σ ^ 2) (M.ζ M.T * 1 / M.σ ^ 2)
            (Icc 0 M.T) t :=
          (((hasDerivAt_id t).const_mul (M.ζ M.T)).div_const (M.σ ^ 2)).hasDerivWithinAt
        refine ((hinvu t ht).add hlin).congr_deriv ?_
        rw [hDu t ht, hα1]
        field_simp
        ring)
    have hform : ∀ t ∈ Icc 0 M.T,
        1 + (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t) = 1 / (1 + (M.ζ t * m₂ t)) := by
      intro t ht
      have := hr t ht
      simp only [huT, add_zero, div_one] at this
      field_simp at this ⊢
      linarith
    intro t ht
    have hf := hform t ht
    have hp := (hp1 t ht).ne'
    have hz0 := (zpos t ht).ne'
    refine ⟨?_, ?_⟩
    · rw [hf]
      field_simp
      ring
    · rw [hf]
      have hd := hDu t ht
      simp only [hα1, one_mul] at hd
      rw [div_div_eq_mul_div, div_one]
      linarith
  · ------------------------------------------------------------------ case α ∉ {0, 1}
    have hα1' : M.α - 1 ≠ 0 := sub_ne_zero.2 hα1
    set c₁ : ℝ := M.α / (M.α - 1) with hc₁
    set c₂ : ℝ := -1 / (M.α - 1) with hc₂
    -- `log D - [u/(1+u) + c₁ log(1+u) + c₂ log(1+αu)]` is constant
    have hk := eq_of_deriv_zero
      (f := fun s => Real.log ((M.ζ s)⁻¹ - M.α * m₃ s) - ((M.ζ s * m₂ s) / (1 + (M.ζ s * m₂ s)) + c₁ * Real.log (1 + (M.ζ s * m₂ s))
        + c₂ * Real.log (1 + M.α * (M.ζ s * m₂ s)))) hT.le
      (fun t ht => by
        have hp := (hp1 t ht).ne'
        have hq := (hp2 t ht).ne'
        have hDt := (hD t ht).ne'
        have d1 := (hDd t ht).log hDt
        have d2 := (hu t ht).div ((hu t ht).const_add 1) hp
        have d3 := ((hu t ht).const_add 1).log hp
        have d4 := (((hu t ht).const_mul M.α).const_add 1).log hq
        refine (d1.sub ((d2.add (d3.const_mul c₁)).add (d4.const_mul c₂))).congr_deriv ?_
        generalize (M.ζ t)⁻¹ - M.α * m₃ t = Dv at hDt ⊢
        generalize M.ζ t * m₂ t = U at hp hq ⊢
        rw [hc₁, hc₂]
        field_simp
        ring)
    have hDE : ∀ t ∈ Icc 0 M.T, ((M.ζ t)⁻¹ - M.α * m₃ t) = (M.ζ M.T)⁻¹ * (Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t)))
        * (1 + (M.ζ t * m₂ t)) ^ c₁ * (1 + M.α * (M.ζ t * m₂ t)) ^ c₂) := by
      intro t ht
      have := hk t ht
      simp only [huT, hDT, add_zero, zero_div, mul_zero, Real.log_one] at this
      have hlogD : Real.log ((M.ζ t)⁻¹ - M.α * m₃ t) = Real.log (M.ζ M.T)⁻¹ +
          ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t)) + c₁ * Real.log (1 + (M.ζ t * m₂ t)) + c₂ * Real.log (1 + M.α * (M.ζ t * m₂ t))) := by
        linarith
      have hDpos := hD t ht
      rw [← Real.exp_log hDpos, hlogD, Real.exp_add, Real.exp_log (inv_pos.2 zT),
        Real.rpow_def_of_pos (hp1 t ht), Real.rpow_def_of_pos (hp2 t ht),
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    -- the function `1/ψ` near the trajectory
    set S : Set ℝ := {y | 0 < 1 - y ∧ 0 < 1 - M.α * y} with hS
    have hSo : IsOpen S := by
      show IsOpen ({y : ℝ | 0 < 1 - y} ∩ {y : ℝ | 0 < 1 - M.α * y})
      exact (isOpen_lt continuous_const (by fun_prop : Continuous fun y : ℝ => 1 - y)).inter
        (isOpen_lt continuous_const (by fun_prop : Continuous fun y : ℝ => 1 - M.α * y))
    have hψpos : ∀ y ∈ S, 0 < ψ M y := by
      intro y hy
      unfold ψ
      have := hy.1; have := hy.2
      positivity
    have hψc : ContinuousOn (fun y => 1 / ψ M y) S := by
      apply ContinuousOn.div continuousOn_const _ (fun y hy => (hψpos y hy).ne')
      unfold ψ
      apply ContinuousOn.mul
      apply ContinuousOn.mul
      · apply ContinuousOn.rexp
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro y hy; exact hy.1.ne'
      · apply ContinuousOn.rpow_const (by fun_prop)
        intro y hy; exact Or.inl hy.1.ne'
      · apply ContinuousOn.rpow_const (by fun_prop)
        intro y hy; exact Or.inl hy.2.ne'
    have hunp : ∀ t ∈ Icc 0 M.T, (M.ζ t * m₂ t) ≤ 0 := by
      intro t ht
      rcases ht.2.lt_or_eq with h' | h'
      · exact (hneg t ⟨ht.1, h'⟩).le
      · rw [h', huT]
    have hxS : ∀ t ∈ Icc 0 M.T, ∀ y ∈ uIcc 0 (-(M.ζ t * m₂ t)), y ∈ S := by
      intro t ht y hy
      have hx0 : 0 ≤ -(M.ζ t * m₂ t) := by linarith [hunp t ht]
      rw [uIcc_of_le hx0] at hy
      have h1 := hp1 t ht
      have h2' := hp2 t ht
      refine ⟨by linarith [hy.2], ?_⟩
      rcases le_total 0 M.α with hα0' | hα0'
      · nlinarith [hy.1, hy.2]
      · nlinarith [hy.1, hy.2]
    have hΨd : ∀ t ∈ Icc 0 M.T, HasDerivAt (Ψ M) (1 / ψ M (-(M.ζ t * m₂ t))) (-(M.ζ t * m₂ t)) := by
      intro t ht
      have hmem : -(M.ζ t * m₂ t) ∈ S := hxS t ht (-(M.ζ t * m₂ t)) right_mem_uIcc
      apply intervalIntegral.integral_hasDerivAt_right
      · exact (hψc.mono (hxS t ht)).intervalIntegrable
      · exact hψc.stronglyMeasurableAtFilter hSo _ hmem
      · exact hψc.continuousAt (hSo.mem_nhds hmem)
    have hEψ : ∀ t ∈ Icc 0 M.T, (Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t))) * (1 + (M.ζ t * m₂ t)) ^ c₁
        * (1 + M.α * (M.ζ t * m₂ t)) ^ c₂) * ψ M (-(M.ζ t * m₂ t)) = (1 + (M.ζ t * m₂ t)) ^ 2 * (1 + M.α * (M.ζ t * m₂ t)) := by
      intro t ht
      have hp := hp1 t ht
      have hq := hp2 t ht
      unfold ψ
      rw [show (1 : ℝ) - -(M.ζ t * m₂ t) = 1 + (M.ζ t * m₂ t) by ring, show 1 - M.α * -(M.ζ t * m₂ t) = 1 + M.α * (M.ζ t * m₂ t) by ring,
        show -(M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t)) = -((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t))) by ring, Real.exp_neg]
      have e1 : (1 + (M.ζ t * m₂ t)) ^ c₁ * (1 + (M.ζ t * m₂ t)) ^ ((M.α - 2) / (M.α - 1)) = (1 + (M.ζ t * m₂ t)) ^ 2 := by
        rw [← Real.rpow_add hp, show c₁ + (M.α - 2) / (M.α - 1) = ((2 : ℕ) : ℝ) by
          rw [hc₁]; field_simp; ring, Real.rpow_natCast]
      have e2 : (1 + M.α * (M.ζ t * m₂ t)) ^ c₂ * (1 + M.α * (M.ζ t * m₂ t)) ^ (M.α / (M.α - 1)) = 1 + M.α * (M.ζ t * m₂ t) := by
        rw [← Real.rpow_add hq, show c₂ + M.α / (M.α - 1) = 1 by
          rw [hc₂]; field_simp; ring, Real.rpow_one]
      have hexp := Real.exp_pos ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t)))
      calc Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t))) * (1 + (M.ζ t * m₂ t)) ^ c₁ * (1 + M.α * (M.ζ t * m₂ t)) ^ c₂ *
            ((Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t))))⁻¹ * (1 + (M.ζ t * m₂ t)) ^ ((M.α - 2) / (M.α - 1)) *
              (1 + M.α * (M.ζ t * m₂ t)) ^ (M.α / (M.α - 1)))
          = (Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t))) * (Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t))))⁻¹)
            * ((1 + (M.ζ t * m₂ t)) ^ c₁ * (1 + (M.ζ t * m₂ t)) ^ ((M.α - 2) / (M.α - 1)))
            * ((1 + M.α * (M.ζ t * m₂ t)) ^ c₂ * (1 + M.α * (M.ζ t * m₂ t)) ^ (M.α / (M.α - 1))) := by ring
        _ = _ := by rw [e1, e2, mul_inv_cancel₀ hexp.ne', one_mul]
    have hΨc := eq_of_deriv_zero
      (f := fun s => Ψ M (-(M.ζ s * m₂ s)) + M.ζ M.T * s / M.σ ^ 2) hT.le
      (fun t ht => by
        have hcomp := (hΨd t ht).comp_hasDerivWithinAt t (hu t ht).neg
        have hlin : HasDerivWithinAt (fun s => M.ζ M.T * s / M.σ ^ 2) (M.ζ M.T * 1 / M.σ ^ 2)
            (Icc 0 M.T) t :=
          (((hasDerivAt_id t).const_mul (M.ζ M.T)).div_const (M.σ ^ 2)).hasDerivWithinAt
        refine (hcomp.add hlin).congr_deriv ?_
        have hE := hEψ t ht
        have hψ0 := (hψpos (-(M.ζ t * m₂ t)) (hxS t ht (-(M.ζ t * m₂ t)) right_mem_uIcc)).ne'
        have hDt := hDE t ht
        have hEpos : 0 < Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t)))
            * (1 + (M.ζ t * m₂ t)) ^ c₁ * (1 + M.α * (M.ζ t * m₂ t)) ^ c₂ :=
          mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hp1 t ht) _))
            (Real.rpow_pos_of_pos (hp2 t ht) _)
        rw [hDt]
        generalize Real.exp ((M.ζ t * m₂ t) / (1 + (M.ζ t * m₂ t)))
            * (1 + (M.ζ t * m₂ t)) ^ c₁ * (1 + M.α * (M.ζ t * m₂ t)) ^ c₂ = E at hE hEpos ⊢
        generalize ψ M (-(M.ζ t * m₂ t)) = Ps at hE hψ0 ⊢
        rw [← hE]
        have hE0 := hEpos.ne'
        have hzT := zT.ne'
        field_simp
        ring)
    intro t ht
    have hp := hp1 t ht
    have hq := hp2 t ht
    refine ⟨⟨by linarith [hunp t ht], ?_⟩, ?_, ?_⟩
    · rcases le_total M.α 1 with hle | hle
      · rw [max_eq_right hle]; linarith
      · rw [max_eq_left hle]
        have hαpos : 0 < M.α := by linarith
        rw [lt_div_iff₀ hαpos]
        linarith
    · have := hΨc t ht
      simp only [huT, neg_zero] at this
      have hΨ0 : Ψ M 0 = 0 := by simp [Ψ]
      rw [hΨ0] at this
      field_simp at this ⊢
      linarith
    · have hd := hDE t ht
      have hαne : M.α ≠ 0 := hα0
      rw [show 1 + M.α * M.ζ t * m₂ t = 1 + M.α * (M.ζ t * m₂ t) by ring]
      rw [show (M.ζ M.T)⁻¹ * Real.exp (M.ζ t * m₂ t / (1 + M.ζ t * m₂ t))
          * (1 + M.ζ t * m₂ t) ^ (M.α / (M.α - 1))
          * (1 + M.α * (M.ζ t * m₂ t)) ^ (-1 / (M.α - 1))
          = (M.ζ M.T)⁻¹ * (Real.exp (M.ζ t * m₂ t / (1 + M.ζ t * m₂ t))
          * (1 + M.ζ t * m₂ t) ^ c₁ * (1 + M.α * (M.ζ t * m₂ t)) ^ c₂) by rw [hc₁, hc₂]; ring,
        ← hd]
      field_simp
      ring
