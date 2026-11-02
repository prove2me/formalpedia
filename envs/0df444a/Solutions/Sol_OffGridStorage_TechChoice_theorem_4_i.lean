-- Prove2me | solution 1 for OffGridStorage.TechChoice.theorem_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:23:58.420457+00:00
-- url     : https://prove2.me/submissions/f3931e87-7eba-48d1-bb88-a7856bd8a27a

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model
import Theorems.Thm_OffGridStorage_TechChoice_theorem_3_concave
import Theorems.Thm_OffGridStorage_TechChoice_eq_20_closed_form
import Theorems.Thm_OffGridStorage_TechChoice_eq_25_marginal_storage
import Theorems.Thm_OffGridStorage_TechChoice_tracking_le_full
import Theorems.Thm_OffGridStorage_TechChoice_tracking_eq_full
import Theorems.Thm_OffGridStorage_TechChoice_eq_19_threshold_ratio
import Theorems.Thm_OffGridStorage_TechChoice_lemma_1_ii

open OffGridStorage.TechChoice Filter Topology

theorem solution (p : Params) (hp : Standing p) (hg : p.g ≤ g0 p) :
    IsOptimalF p (Q0 p) 0 ∧ IsOptimalTR p (Q0 p) 0 ∧
      profitTR p (Q0 p) 0 = profitF p (Q0 p) 0 := by
  have hp' := hp
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hgc, hT⟩ := hp'
  have hr : 0 ≤ p.cK / p.e := div_nonneg hcK he0.le
  have hgpos : 0 < p.g := by linarith
  -- marginal value of storage at (Q0, 0) is nonpositive
  have hc0 : p.g - Real.sqrt (2 * p.cQ * p.g) - p.cK / p.e ≤ 0 := by
    have h1 : ¬ (g0ratio p.cQ (p.cK / p.e) < p.g) := by
      rw [← lemma_1_ii.1]; exact not_lt.mpr hg
    rw [(eq_19_threshold_ratio p.cQ _ p.g hcQ hr hgc).2] at h1
    linarith [not_lt.mp h1]
  obtain ⟨⟨hQ00, hQ0max⟩, -, -⟩ := eq_25_marginal_storage p hp
  have hsq1 : 1 < Real.sqrt (p.g / (2 * p.cQ)) := by
    rw [Real.lt_sqrt (by norm_num), one_pow, lt_div_iff₀ (by linarith)]; linarith
  have hQ0DH : p.DH < Q0 p := by unfold Q0; nlinarith
  have hQ0pos : 0 < Q0 p := by linarith
  -- g * DH / Q0 = √(2 cQ g)
  have hid : p.g * p.DH / Q0 p = Real.sqrt (2 * p.cQ * p.g) := by
    unfold Q0
    have hs : Real.sqrt (p.g / (2 * p.cQ)) * Real.sqrt (2 * p.cQ * p.g) = p.g := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show p.g / (2 * p.cQ) * (2 * p.cQ * p.g) = p.g ^ 2 by field_simp]
      exact Real.sqrt_sq hgpos.le
    have hpos : 0 < Real.sqrt (p.g / (2 * p.cQ)) := by linarith
    rw [div_eq_iff (by positivity), show Real.sqrt (2 * p.cQ * p.g) * (p.DH *
      Real.sqrt (p.g / (2 * p.cQ))) = p.DH * (Real.sqrt (p.g / (2 * p.cQ)) *
      Real.sqrt (2 * p.cQ * p.g)) by ring, hs]
    ring
  have hconc := (theorem_3_concave p hp).2
  have hF : IsOptimalF p (Q0 p) 0 := by
    refine ⟨hQ00, le_rfl, ?_⟩
    intro Q' K' hQ' hK'
    set Qt : ℝ → ℝ := fun t => (1 - t) * Q0 p + t * Q' with hQt
    set φ : ℝ → ℝ := fun t => (p.T : ℝ) * K' * (p.g - p.g * p.DH / Qt t - p.cK / p.e) with hφ
    have hQtc : Continuous Qt := by simp only [hQt]; fun_prop
    have hQt0 : Qt 0 = Q0 p := by simp [hQt]
    have hφc : ContinuousAt φ 0 := by
      simp only [hφ]
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.sub _ continuousAt_const
      apply ContinuousAt.sub continuousAt_const
      apply ContinuousAt.div continuousAt_const hQtc.continuousAt
      rw [hQt0]; exact hQ0pos.ne'
    have hφ0 : φ 0 = (p.T : ℝ) * K' * (p.g - Real.sqrt (2 * p.cQ * p.g) - p.cK / p.e) := by
      simp only [hφ, hQt0, hid]
    have hlim : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) := hφc.tendsto.mono_left nhdsWithin_le_nhds
    -- eventually the region conditions hold
    have hreg : Tendsto (fun t => Qt t - p.DH - t * K' / p.e) (𝓝 0) (𝓝 (Q0 p - p.DH)) := by
      have : Continuous (fun t => Qt t - p.DH - t * K' / p.e) := by
        simp only [hQt]; fun_prop
      have h := this.tendsto 0
      simpa [hQt0] using h
    have ev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < Qt t - p.DH - t * K' / p.e :=
      nhdsWithin_le_nhds (hreg.eventually (lt_mem_nhds (by linarith)))
    have ev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 := nhdsWithin_le_nhds (gt_mem_nhds one_pos)
    have ev3 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ), profitF p Q' K' - profitF p (Q0 p) 0 ≤ φ t := by
      filter_upwards [ev1, ev2, ev3] with t h1 h2 h3
      have hkt : 0 ≤ t * K' := mul_nonneg h3.le hK'
      have hQtpos : p.DH < Qt t := by
        have : 0 ≤ t * K' / p.e := div_nonneg hkt he0.le
        linarith
      have hQtnn : 0 ≤ Qt t := by linarith
      -- concavity along the segment
      have hc := hconc (x := (Q0 p, 0)) ⟨hQ00, le_rfl⟩ (y := (Q', K')) ⟨hQ', hK'⟩
        (a := 1 - t) (b := t) (by linarith) h3.le (by ring)
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero, zero_add] at hc
      -- closed forms
      have e1 : profitF p (Qt t) (t * K') = closedFormF p (Qt t) (t * K') :=
        eq_20_closed_form p hp (Qt t) (t * K') hkt (by
          have : p.DH + t * K' / p.e ≤ Qt t := by linarith
          simpa [mul_div_assoc] using this)
      have e2 : profitF p (Qt t) 0 = closedFormF p (Qt t) 0 :=
        eq_20_closed_form p hp (Qt t) 0 le_rfl (by simp; linarith)
      have hmax := hQ0max (Qt t) hQtnn
      have hdiff : closedFormF p (Qt t) (t * K') - closedFormF p (Qt t) 0 ≤
          t * φ t := by
        simp only [hφ]
        unfold closedFormF
        have hQ := hQtpos
        have hQp : 0 < Qt t := by linarith
        have hT0 : (0:ℝ) ≤ p.T := Nat.cast_nonneg _
        have hsq : 0 ≤ p.g / Qt t * ((t * K') ^ 2 / (2 * p.e)) := by positivity
        have : p.g / Qt t * (-p.DH ^ 2 / 2 - (t * K') ^ 2 / (2 * p.e) - t * K' * p.DH) -
            p.g / Qt t * (-p.DH ^ 2 / 2 - 0 ^ 2 / (2 * p.e) - 0 * p.DH) =
            - (p.g / Qt t * ((t * K') ^ 2 / (2 * p.e))) - t * K' * (p.g * p.DH / Qt t) := by
          field_simp; ring
        have h4 : (p.T : ℝ) * (p.g / Qt t * (-p.DH ^ 2 / 2 - (t * K') ^ 2 / (2 * p.e) - t * K' * p.DH)
            + p.g * (p.DH + t * K') - p.cK / p.e * (t * K') - p.cQ * Qt t) -
            (p.T : ℝ) * (p.g / Qt t * (-p.DH ^ 2 / 2 - 0 ^ 2 / (2 * p.e) - 0 * p.DH)
            + p.g * (p.DH + 0) - p.cK / p.e * 0 - p.cQ * Qt t) =
            (p.T : ℝ) * (-(p.g / Qt t * ((t * K') ^ 2 / (2 * p.e)))) +
            t * ((p.T : ℝ) * K' * (p.g - p.g * p.DH / Qt t - p.cK / p.e)) := by
          linear_combination (p.T : ℝ) * this
        rw [h4]
        nlinarith [mul_nonneg hT0 hsq]
      have hseg : (1 - t) * profitF p (Q0 p) 0 + t * profitF p Q' K' ≤
          profitF p (Qt t) (t * K') := by simpa [hQt] using hc
      have : t * (profitF p Q' K' - profitF p (Q0 p) 0) ≤ t * φ t := by nlinarith
      exact le_of_mul_le_mul_left this h3
    have := ge_of_tendsto hlim hbound
    rw [hφ0] at this
    have hT0 : (0:ℝ) ≤ p.T := Nat.cast_nonneg _
    have : (p.T : ℝ) * K' * (p.g - Real.sqrt (2 * p.cQ * p.g) - p.cK / p.e) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hT0 hK') hc0
    linarith
  have heq : profitTR p (Q0 p) 0 = profitF p (Q0 p) 0 :=
    tracking_eq_full p hp (Q0 p) 0 hQ00 le_rfl hDL.le
  refine ⟨hF, ⟨hQ00, le_rfl, ?_⟩, heq⟩
  intro Q' K' hQ' hK'
  have := tracking_le_full p hp Q' K' hQ' hK'
  have := hF.2.2 Q' K' hQ' hK'
  linarith
