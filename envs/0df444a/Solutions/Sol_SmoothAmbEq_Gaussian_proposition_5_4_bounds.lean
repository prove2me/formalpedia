-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.proposition_5_4_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:12:33.286992+00:00
-- url     : https://prove2.me/submissions/1efcb056-0e60-4296-899c-2863844bb340

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SAEBounds

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

end SAEBounds

open SmoothAmbEq.Gaussian SAEBounds

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    ∀ t ∈ Ico 0 M.T,
      0 > M.ζ t * m₂ t ∧ M.ζ t * m₂ t > -(1 / max M.α 1) ∧ m₃ t < 0 ∧
      (M.ζ t)⁻¹ - M.α * m₃ t > 0 := by
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
  -- `m₃` is strictly increasing on `[0, T]`
  have hm3mono : StrictMonoOn m₃ (Icc 0 M.T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 M.T) c3
    intro t ht
    rw [interior_Icc] at ht
    have hd := (h3 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [hd.deriv]
    have h1 := hp1 t (Ioo_subset_Icc_self ht)
    have h0 := hulT t ⟨ht.1.le, ht.2⟩
    have e : -2 * M.ζ t * m₂ t - M.ζ t ^ 2 * m₂ t ^ 2 = -(u t) * (2 + u t) := by
      simp only [hudef]; ring
    rw [e]
    apply div_pos _ hσ2
    apply mul_pos (by linarith) (by linarith)
  intro t ht
  have htI : t ∈ Icc 0 M.T := ⟨ht.1, ht.2.le⟩
  refine ⟨hulT t ht, ?_, ?_, hD t htI⟩
  · -- lower bound
    have h1 := hp1 t htI
    have h2' := hp2 t htI
    show u t > -(1 / max α 1)
    rcases le_total α 1 with hα1 | hα1
    · rw [max_eq_right hα1]; linarith
    · rw [max_eq_left hα1]
      have hαpos : 0 < α := by linarith
      rw [gt_iff_lt, neg_lt, ← sub_pos]
      have : 1 / α + u t = (1 + α * u t) / α := by field_simp
      rw [show 1 / α - -u t = 1 / α + u t by ring, this]
      positivity
  · have := hm3mono htI ⟨hT.le, le_rfl⟩ ht.2
    rwa [h3T] at this
