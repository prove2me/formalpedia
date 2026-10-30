-- Prove2me | solution 1 for PricingSamples.OneSampleMHR.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:57:18.107452+00:00
-- url     : https://prove2.me/submissions/146eeaa5-f938-4810-834b-c0536e3c80ac

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

namespace PSMH

open MeasureTheory PricingSamples.OneSampleMHR

lemma ccdf_anti (μ : Measure ℝ) [IsFiniteMeasure μ] {x y : ℝ} (h : x ≤ y) :
    ccdf μ y ≤ ccdf μ x := by
  unfold ccdf
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ioi_subset_Ioi h))

lemma ccdf_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ ccdf μ x := ENNReal.toReal_nonneg

lemma GammaA_GammaAInv {α y : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hy : 0 < y) :
    GammaA α (GammaAInv α y) = y := by
  unfold GammaA GammaAInv
  by_cases h1 : α = 1
  · simp [h1, Real.exp_log hy]
  · simp only [h1, if_false]
    have hb : 0 < 1 - α := by
      rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    have e : 1 + (1 - α) * ((y ^ (-(1 - α)) - 1) / (1 - α)) = y ^ (-(1 - α)) := by
      field_simp; ring
    rw [e, ← Real.rpow_mul hy.le]
    have : -(1 - α) * -(1 / (1 - α)) = 1 := by field_simp
    rw [this, Real.rpow_one]

lemma GammaAInv_div {α x q : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hx : 0 < x) (hq : 0 < q) :
    GammaAInv α (x / q) = q ^ (1 - α) * (GammaAInv α x - GammaAInv α q) := by
  unfold GammaAInv
  by_cases h1 : α = 1
  · simp only [h1, if_true, sub_self, Real.rpow_zero, one_mul]
    rw [Real.log_div hx.ne' hq.ne']; ring
  · simp only [h1, if_false]
    have hb : 0 < 1 - α := by
      rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    rw [Real.div_rpow hx.le hq.le, Real.rpow_neg hq.le]
    have hA : 0 < q ^ (1 - α) := Real.rpow_pos_of_pos hq _
    field_simp
    ring

lemma GammaAInv_nonneg {α y : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ GammaAInv α y := by
  unfold GammaAInv
  by_cases h1 : α = 1
  · simp only [h1, if_true]
    have := Real.log_nonpos hy.le hy1
    linarith
  · simp only [h1, if_false]
    have hb : 0 < 1 - α := by
      rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith : -(1 - α) ≤ 0)
    apply div_nonneg _ hb.le
    linarith

lemma GammaA_nonneg {α x : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hx : 0 ≤ x) : 0 ≤ GammaA α x := by
  unfold GammaA
  split_ifs
  · exact (Real.exp_pos _).le
  · apply Real.rpow_nonneg
    have : 0 ≤ 1 - α := by linarith [hα.2]
    nlinarith

lemma GammaA_anti {α x y : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    GammaA α y ≤ GammaA α x := by
  unfold GammaA
  by_cases h1 : α = 1
  · simp only [h1, if_true]
    exact Real.exp_le_exp.mpr (by linarith)
  · simp only [h1, if_false]
    have hb : 0 < 1 - α := by
      rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    apply Real.rpow_le_rpow_of_nonpos
    · nlinarith
    · nlinarith
    · have : 0 < 1 / (1 - α) := by positivity
      linarith

end PSMH

open MeasureTheory PricingSamples.OneSampleMHR PSMH

theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) (hF : InFAlpha α μ)
    (w w' : ℝ) (hw : 0 ≤ w) (hww' : w < w') :
    (∀ v, w ≤ v → v ≤ w' → Galpha α w (ccdf μ w) w' (ccdf μ w') v ≤ ccdf μ v) ∧
      (∀ v, w' ≤ v → ccdf μ v ≤ Galpha α w (ccdf μ w) w' (ccdf μ w') v) := by
  obtain ⟨⟨hprob, -, -, -⟩, -, hconv⟩ := hF
  have hq'q : ccdf μ w' ≤ ccdf μ w := ccdf_anti μ hww'.le
  by_cases hq'0 : ccdf μ w' = 0
  · constructor
    · intro v hv1 hv2
      unfold Galpha
      rw [if_pos hq'0]
      split_ifs with h
      · rw [le_antisymm h hv1]
      · exact ccdf_nonneg μ v
    · intro v hv
      unfold Galpha
      rw [if_pos hq'0]
      split_ifs with h
      · exact absurd (lt_of_lt_of_le hww' hv) (not_lt.mpr h)
      · rw [← hq'0]; exact ccdf_anti μ hv
  have hq'pos : 0 < ccdf μ w' := lt_of_le_of_ne (ccdf_nonneg μ _) (Ne.symm hq'0)
  have hqpos : 0 < ccdf μ w := lt_of_lt_of_le hq'pos hq'q
  set q := ccdf μ w with hqdef
  set q' := ccdf μ w' with hq'def
  set φ : ℝ → ℝ := fun v => GammaAInv α (ccdf μ v) with hφ
  set c := q ^ (1 - α) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hqpos _
  have hψ : ∀ v, 0 < ccdf μ v → GammaAInv α (ccdf μ v / q) = c * (φ v - φ w) := by
    intro v hv
    exact GammaAInv_div hα hv hqpos
  have hK : GammaAInv α (q' / q) = c * (φ w' - φ w) := hψ w' hq'pos
  have hrep : ∀ v, 0 < ccdf μ v → ccdf μ v = q * GammaA α (c * (φ v - φ w)) := by
    intro v hv
    rw [← hψ v hv, GammaA_GammaAInv hα (div_pos hv hqpos)]
    field_simp
  have hψnn : ∀ v, w ≤ v → 0 < ccdf μ v → 0 ≤ c * (φ v - φ w) := by
    intro v hv1 hv2
    rw [← hψ v hv2]
    exact GammaAInv_nonneg hα (div_pos hv2 hqpos) ((div_le_one hqpos).mpr (ccdf_anti μ hv1))
  have hKnn : 0 ≤ c * (φ w' - φ w) := hψnn w' hww'.le hq'pos
  have hwS : w ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨hw, hqpos⟩
  have hw'S : w' ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨by linarith, hq'pos⟩
  have hG : ∀ v, Galpha α w q w' q' v = q * GammaA α (c * (φ w' - φ w) * ((v - w) / (w' - w))) := by
    intro v
    unfold Galpha
    rw [if_neg hq'0, hK]
  have hd : 0 < w' - w := sub_pos.mpr hww'
  constructor
  · intro v hv1 hv2
    have hvpos : 0 < ccdf μ v := lt_of_lt_of_le hq'pos (ccdf_anti μ hv2)
    rw [hG v, hrep v hvpos]
    set b := (v - w) / (w' - w) with hb
    have hb0 : 0 ≤ b := div_nonneg (by linarith) hd.le
    have ha0 : 0 ≤ (w' - v) / (w' - w) := div_nonneg (by linarith) hd.le
    have hab : (w' - v) / (w' - w) + b = 1 := by rw [hb]; field_simp; ring
    have h := hconv.2 hwS hw'S ha0 hb0 hab
    simp only [smul_eq_mul] at h
    have e : (w' - v) / (w' - w) * w + b * w' = v := by rw [hb]; field_simp; ring
    rw [e] at h
    have ea : (w' - v) / (w' - w) = 1 - b := by linarith
    rw [ea] at h
    have h2 : φ v - φ w ≤ b * (φ w' - φ w) := by simp only [hφ] at h ⊢; nlinarith
    have h3 : c * (φ v - φ w) ≤ c * (φ w' - φ w) * b := by
      have := mul_le_mul_of_nonneg_left h2 hc.le
      linarith
    exact mul_le_mul_of_nonneg_left (GammaA_anti hα (hψnn v hv1 hvpos) h3) hqpos.le
  · intro v hv
    have hvw : w < v := lt_of_lt_of_le hww' hv
    have hvw' : 0 < v - w := sub_pos.mpr hvw
    rw [hG v]
    have htnn : 0 ≤ c * (φ w' - φ w) * ((v - w) / (w' - w)) :=
      mul_nonneg hKnn (div_nonneg hvw'.le hd.le)
    by_cases hv0 : ccdf μ v = 0
    · rw [hv0]
      exact mul_nonneg hqpos.le (GammaA_nonneg hα htnn)
    have hvpos : 0 < ccdf μ v := lt_of_le_of_ne (ccdf_nonneg μ _) (Ne.symm hv0)
    have hvS : v ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨by linarith, hvpos⟩
    rw [hrep v hvpos]
    set b := (w' - w) / (v - w) with hb
    have hb0 : 0 ≤ b := div_nonneg hd.le hvw'.le
    have ha0 : 0 ≤ (v - w') / (v - w) := div_nonneg (by linarith) hvw'.le
    have hab : (v - w') / (v - w) + b = 1 := by rw [hb]; field_simp; ring
    have h := hconv.2 hwS hvS ha0 hb0 hab
    simp only [smul_eq_mul] at h
    have e : (v - w') / (v - w) * w + b * v = w' := by rw [hb]; field_simp; ring
    rw [e] at h
    have ea : (v - w') / (v - w) = 1 - b := by linarith
    rw [ea] at h
    have h2 : φ w' - φ w ≤ b * (φ v - φ w) := by simp only [hφ] at h ⊢; nlinarith
    have hbt : b * ((v - w) / (w' - w)) = 1 := by rw [hb]; field_simp
    have h3 : c * (φ w' - φ w) * ((v - w) / (w' - w)) ≤ c * (φ v - φ w) := by
      have h4 := mul_le_mul_of_nonneg_right h2 (div_nonneg hvw'.le hd.le : 0 ≤ (v - w) / (w' - w))
      have h5 : b * (φ v - φ w) * ((v - w) / (w' - w)) = φ v - φ w := by
        calc b * (φ v - φ w) * ((v - w) / (w' - w)) = (b * ((v - w) / (w' - w))) * (φ v - φ w) := by ring
          _ = φ v - φ w := by rw [hbt, one_mul]
      rw [h5] at h4
      have := mul_le_mul_of_nonneg_left h4 hc.le
      linarith
    exact mul_le_mul_of_nonneg_left (GammaA_anti hα htnn h3) hqpos.le
