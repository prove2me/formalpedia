-- Prove2me | solution 1 for PricingSamples.OneSampleMHR.lemma_G_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:00:01.876825+00:00
-- url     : https://prove2.me/submissions/ae9901bc-6533-43df-aa25-a3ef7da81a14

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
namespace PSMH

open MeasureTheory PricingSamples.OneSampleMHR

lemma neg_GammaAInv_ge {α y : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hy : 1 ≤ y) :
    1 - y⁻¹ ≤ -GammaAInv α y := by
  have hy0 : 0 < y := by linarith
  unfold GammaAInv
  by_cases h1 : α = 1
  · simp only [h1, if_true, neg_neg]
    exact Real.one_sub_inv_le_log_of_pos hy0
  · simp only [h1, if_false]
    have hb : 0 < 1 - α := by
      rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    have hb1 : 1 - α ≤ 1 := by linarith [hα.1]
    have hinv : y ^ (-(1 - α)) = (y⁻¹) ^ (1 - α) := by
      rw [Real.rpow_neg hy0.le, Real.inv_rpow hy0.le]
    have hyi : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
    have hyi0 : 0 < y⁻¹ := inv_pos.mpr hy0
    have bern := rpow_one_add_le_one_add_mul_self (by linarith : (-1:ℝ) ≤ y⁻¹ - 1) hb.le hb1
    rw [show 1 + (y⁻¹ - 1) = y⁻¹ by ring] at bern
    rw [hinv]
    rw [show -(((y⁻¹) ^ (1 - α) - 1) / (1 - α)) = (1 - (y⁻¹) ^ (1 - α)) / (1 - α) by ring]
    rw [le_div_iff₀ hb]
    nlinarith

lemma rev_anti {α s w x y : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hs : 0 ≤ s) (hw : 0 < w)
    (hsw : 1 ≤ s * w) (hx : w ≤ x) (hxy : x ≤ y) :
    y * GammaA α (s * (y - w)) ≤ x * GammaA α (s * (x - w)) := by
  have hx0 : 0 < x := by linarith
  have hsx : 1 ≤ s * x := by nlinarith
  unfold GammaA
  by_cases h1 : α = 1
  · simp only [h1, if_true]
    have e : Real.exp (-(s * (y - w))) = Real.exp (-(s * (y - x))) * Real.exp (-(s * (x - w))) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h2 : y ≤ x * Real.exp (s * (y - x)) := by
      have := Real.add_one_le_exp (s * (y - x))
      have h3 : y ≤ x * (s * (y - x) + 1) := by nlinarith
      nlinarith
    have h4 : y * Real.exp (-(s * (y - x))) ≤ x := by
      rw [Real.exp_neg]
      rw [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      exact h2
    have := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-(s * (x - w)))).le
    linarith
  · simp only [h1, if_false]
    set β := 1 - α with hβ
    have hb : 0 < β := by
      rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    have hb1 : β ≤ 1 := by linarith [hα.1]
    set A := 1 + β * (s * (x - w)) with hA
    set B := 1 + β * (s * (y - w)) with hB
    have hA1 : 1 ≤ A := by
      have : 0 ≤ β * (s * (x - w)) := mul_nonneg hb.le (mul_nonneg hs (by linarith))
      linarith
    have hA0 : 0 < A := by linarith
    have hAB : A ≤ B := by
      have : s * (x - w) ≤ s * (y - w) := mul_le_mul_of_nonneg_left (by linarith) hs
      have := mul_le_mul_of_nonneg_left this hb.le
      linarith
    have hB0 : 0 < B := by linarith
    -- A ≤ s * x
    have hAsx : A ≤ s * x := by
      have : s * x - A = (s * w - 1) + (1 - β) * s * (x - w) := by rw [hA]; ring
      have h5 : 0 ≤ (1 - β) * s * (x - w) := mul_nonneg (mul_nonneg (by linarith) hs) (by linarith)
      linarith
    -- (y/x)^β ≤ B/A
    have hyx : 0 ≤ y / x := div_nonneg (by linarith) hx0.le
    have bern := rpow_one_add_le_one_add_mul_self (by
      have : 0 ≤ y / x := hyx
      linarith : (-1:ℝ) ≤ y / x - 1) hb.le hb1
    rw [show 1 + (y / x - 1) = y / x by ring] at bern
    have h6 : 1 + β * (y / x - 1) ≤ B / A := by
      rw [le_div_iff₀ hA0]
      have e1 : y / x - 1 = (y - x) / x := by field_simp
      rw [e1]
      have e2 : B = A + β * s * (y - x) := by rw [hA, hB]; ring
      rw [e2]
      have h7 : A * ((y - x) / x) ≤ s * (y - x) := by
        rw [mul_div_assoc', div_le_iff₀ hx0]
        nlinarith
      nlinarith
    have h8 : (y / x) ^ β ≤ B / A := le_trans bern h6
    have h9 : y / x ≤ (B / A) ^ (1 / β) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hyx β) h8 (by positivity : (0:ℝ) ≤ 1 / β)
      rwa [← Real.rpow_mul hyx, show β * (1 / β) = 1 by field_simp, Real.rpow_one] at this
    rw [Real.div_rpow hB0.le hA0.le] at h9
    have hPA : 0 < A ^ (1 / β) := Real.rpow_pos_of_pos hA0 _
    have hPB : 0 < B ^ (1 / β) := Real.rpow_pos_of_pos hB0 _
    rw [div_le_div_iff₀ hx0 hPA] at h9
    rw [Real.rpow_neg hB0.le, Real.rpow_neg hA0.le, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ hPB hPA]
    linarith

end PSMH

open MeasureTheory PricingSamples.OneSampleMHR PSMH

theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) (hF : InFAlpha α μ)
    (r : ℝ) (hr : IsOptPrice μ r) (w w' : ℝ) (hww' : w < w') (hrw : r < w) :
    AntitoneOn (fun v => v * Galpha α w (ccdf μ w) w' (ccdf μ w') v) (Set.Ici w) := by
  obtain ⟨⟨hprob, -, -, -⟩, -, hconv⟩ := hF
  obtain ⟨hr0, hmax⟩ := hr
  have hmax' : ∀ p, 0 ≤ p → p * ccdf μ p ≤ r * ccdf μ r := fun p hp => hmax (Set.mem_Ici.mpr hp)
  have hw0 : 0 < w := lt_of_le_of_lt hr0 hrw
  have hq'q : ccdf μ w' ≤ ccdf μ w := ccdf_anti μ hww'.le
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  simp only
  by_cases hq'0 : ccdf μ w' = 0
  · unfold Galpha
    rw [if_pos hq'0, if_pos hq'0]
    by_cases h2 : y ≤ w
    · have e1 : x = w := le_antisymm (le_trans hxy h2) hx
      have e2 : y = w := le_antisymm h2 hy
      rw [e1, e2]
    · rw [if_neg h2, mul_zero]
      split_ifs
      · exact mul_nonneg (by linarith) (ccdf_nonneg μ w)
      · simp
  have hq'pos : 0 < ccdf μ w' := lt_of_le_of_ne (ccdf_nonneg μ _) (Ne.symm hq'0)
  have hqpos : 0 < ccdf μ w := lt_of_lt_of_le hq'pos hq'q
  have hqrq : ccdf μ w ≤ ccdf μ r := ccdf_anti μ hrw.le
  have hqr : 0 < ccdf μ r := lt_of_lt_of_le hqpos hqrq
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · have := hmax' w' (by linarith)
      rw [← h, zero_mul] at this
      have := mul_pos (by linarith : (0:ℝ) < w') hq'pos
      linarith
    · exact h
  set q := ccdf μ w with hqdef
  set q' := ccdf μ w' with hq'def
  set φ : ℝ → ℝ := fun v => GammaAInv α (ccdf μ v) with hφ
  set c := q ^ (1 - α) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hqpos _
  have hK : GammaAInv α (q' / q) = c * (φ w' - φ w) := GammaAInv_div hα hq'pos hqpos
  have hR : GammaAInv α (ccdf μ r / q) = c * (φ r - φ w) := GammaAInv_div hα hqr hqpos
  have hrS : r ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨hr0, hqr⟩
  have hwS : w ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨hw0.le, hqpos⟩
  have hw'S : w' ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨by linarith, hq'pos⟩
  have hslope := hconv.slope_mono_adjacent hrS hw'S hrw hww'
  -- the ratio y0 = q_r / q satisfies y0 ≥ 1 and y0⁻¹ ≤ r / w
  set y0 := ccdf μ r / q with hy0
  have hy01 : 1 ≤ y0 := (one_le_div hqpos).mpr hqrq
  have hopt : w * q ≤ r * ccdf μ r := hmax' w hw0.le
  have hy0inv : y0⁻¹ ≤ r / w := by
    rw [hy0, inv_div, div_le_div_iff₀ hqr hw0]
    linarith
  have hneg := neg_GammaAInv_ge hα hy01
  rw [hR] at hneg
  -- s * w ≥ 1
  set s := c * (φ w' - φ w) / (w' - w) with hs
  have hd : 0 < w' - w := sub_pos.mpr hww'
  have hd2 : 0 < w - r := sub_pos.mpr hrw
  have hsl2 : c * ((φ w - φ r) / (w - r)) ≤ s := by
    rw [hs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hslope hc.le
  have hlow : (w - r) / w ≤ c * (φ w - φ r) := by
    have : (w - r) / w = 1 - r / w := by field_simp
    rw [this]
    have : 1 - y0⁻¹ ≤ c * (φ w - φ r) := by linarith
    linarith
  have hsw : 1 ≤ s * w := by
    have h1 : (w - r) / w / (w - r) ≤ c * (φ w - φ r) / (w - r) :=
      div_le_div_of_nonneg_right hlow hd2.le
    have e1 : (w - r) / w / (w - r) = 1 / w := by field_simp
    rw [e1, mul_div_assoc] at h1
    have h2 : 1 / w ≤ s := le_trans h1 hsl2
    rw [div_le_iff₀ hw0] at h2
    linarith
  have hs0 : 0 ≤ s := by
    apply div_nonneg _ hd.le
    rw [← hK]
    exact GammaAInv_nonneg hα (div_pos hq'pos hqpos) ((div_le_one hqpos).mpr hq'q)
  have hG : ∀ v, Galpha α w q w' q' v = q * GammaA α (s * (v - w)) := by
    intro v
    unfold Galpha
    rw [if_neg hq'0, hK, hs]
    congr 2
    field_simp
  rw [hG x, hG y]
  have := rev_anti hα hs0 hw0 hsw hx hxy
  have := mul_le_mul_of_nonneg_left this hqpos.le
  linarith
