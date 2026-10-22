-- Prove2me | solution 1 for SuReturns.PartialRefunds.proposition1_full_refund
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:23:51.300475+00:00
-- url     : https://prove2.me/submissions/c4ca04cd-ffa7-4e62-933f-bba3e9a15e91

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory SuReturns.PartialRefunds SupplyChainTheory

lemma sr_nonneg_ae (D : Measure ℝ) (hD0 : D (Set.Iio 0) = 0) : ∀ᵐ d ∂D, 0 ≤ d := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
  rw [this]; exact hD0

lemma sr_int (D : Measure ℝ) [IsProbabilityMeasure D] (hD0 : D (Set.Iio 0) = 0) (q : ℝ) :
    Integrable (fun d => min q d) D := by
  refine (integrable_const |q|).mono' ((measurable_const.min measurable_id).aestronglyMeasurable) ?_
  filter_upwards [sr_nonneg_ae D hD0] with d hd
  rw [Real.norm_eq_abs]
  rcases le_total q d with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hd]
    exact h.trans (le_abs_self q)

lemma sr_sales_nonneg (D : Measure ℝ) (hD0 : D (Set.Iio 0) = 0) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ expSales D q := by
  unfold expSales
  refine integral_nonneg_of_ae ?_
  filter_upwards [sr_nonneg_ae D hD0] with d hd
  exact le_min hq hd

lemma sr_supergrad (D : Measure ℝ) [IsProbabilityMeasure D] (hD0 : D (Set.Iio 0) = 0) (q q0 : ℝ) :
    expSales D q - expSales D q0 ≤ (q - q0) * (1 - cdf D q0) := by
  unfold expSales
  rw [← integral_sub (sr_int D hD0 q) (sr_int D hD0 q0)]
  have hind : Integrable (fun d : ℝ => (q - q0) * (Set.Ioi q0).indicator (fun _ => (1 : ℝ)) d) D :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi).const_mul _
  have hle : ∫ d, (min q d - min q0 d) ∂D ≤
      ∫ d, (q - q0) * (Set.Ioi q0).indicator (fun _ => (1 : ℝ)) d ∂D := by
    refine integral_mono ((sr_int D hD0 q).sub (sr_int D hD0 q0)) hind (fun d => ?_)
    by_cases h : q0 < d
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 h), min_eq_left h.le]
      have := min_le_left q d
      linarith
    · rw [Set.indicator_of_notMem (by simpa using h), mul_zero]
      have h' : d ≤ q0 := not_lt.1 h
      rw [min_eq_right h']
      have := min_le_right q d
      linarith
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one,
    cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]

lemma sr_ret (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) :
    returnProb ν p = 1 - keepProb ν p := by
  unfold returnProb keepProb
  have h := probReal_compl_eq_one_sub (μ := ν) (measurableSet_Ici : MeasurableSet (Set.Ici p))
  rw [Set.compl_Ici] at h
  simpa [Measure.real] using h

lemma sr_profit (ν D : Measure ℝ) [IsProbabilityMeasure ν] (c s p q : ℝ) :
    fullRefundProfit ν D c s p q = ((p - s) * keepProb ν p) * expSales D q - (c - s) * q := by
  unfold fullRefundProfit
  rw [sr_ret]
  ring

lemma sr_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable (fun v => v) ν)
    (c s : ℝ) (hsc : s < c) (hcμ : c < meanValuation ν) : ∃ p, s < p ∧ 0 < keepProb ν p := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ p, s < p → ν (Set.Ici p) = 0 := by
    intro p hp
    have h1 := hcon p hp
    have h2 : 0 ≤ keepProb ν p := ENNReal.toReal_nonneg
    have h3 : (ν (Set.Ici p)).toReal = 0 := le_antisymm h1 h2
    rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hnull : ν (Set.Ioi s) = 0 := by
    refine measure_mono_null (fun v hv => ?_)
      (measure_iUnion_null (fun n : ℕ => hzero (s + 1 / ((n : ℝ) + 1)) (lt_add_of_pos_right _ (by positivity))))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (Set.mem_Ioi.1 hv))
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [Set.mem_Ici]
    linarith
  have hae : ∀ᵐ v ∂ν, v ≤ s := by
    rw [ae_iff]
    have : {a : ℝ | ¬ a ≤ s} = Set.Ioi s := by ext a; simp
    rw [this]; exact hnull
  have : meanValuation ν ≤ s := by
    unfold meanValuation
    calc ∫ v, v ∂ν ≤ ∫ _v, s ∂ν := integral_mono_ae hν (integrable_const s) hae
      _ = s := by simp
  linarith

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (pF qF : ℝ) (hp : IsMaxOn (fun p => (p - s) * keepProb ν p) Set.univ pF)
    (hq : 1 - cdf D qF = (c - s) / ((pF - s) * keepProb ν pF)) :
    ∀ p q, 0 ≤ q → fullRefundProfit ν D c s p q ≤ fullRefundProfit ν D c s pF qF := by
  intro p q hq0
  rw [sr_profit ν D c s p q, sr_profit ν D c s pF qF]
  have hm : (p - s) * keepProb ν p ≤ (pF - s) * keepProb ν pF := isMaxOn_univ_iff.1 hp p
  obtain ⟨p1, hp1, hk1⟩ := sr_pos ν hν c s hsc hcμ
  have hmspos : 0 < (pF - s) * keepProb ν pF :=
    lt_of_lt_of_le (mul_pos (sub_pos.2 hp1) hk1) (isMaxOn_univ_iff.1 hp p1)
  have h1 : ((p - s) * keepProb ν p) * expSales D q ≤ ((pF - s) * keepProb ν pF) * expSales D q :=
    mul_le_mul_of_nonneg_right hm (sr_sales_nonneg D hD0 q hq0)
  have hms' : ((pF - s) * keepProb ν pF) * (1 - cdf D qF) = c - s := by
    have key : ∀ M : ℝ, 0 < M → M * ((c - s) / M) = c - s := fun M hM => by field_simp
    rw [hq]; exact key _ hmspos
  have h2 := sr_supergrad D hD0 q qF
  have h3 : ((pF - s) * keepProb ν pF) * (expSales D q - expSales D qF) ≤ (q - qF) * (c - s) := by
    calc ((pF - s) * keepProb ν pF) * (expSales D q - expSales D qF)
        ≤ ((pF - s) * keepProb ν pF) * ((q - qF) * (1 - cdf D qF)) :=
          mul_le_mul_of_nonneg_left h2 hmspos.le
      _ = (q - qF) * (c - s) := by rw [← hms']; ring
  nlinarith [h1, h3]
