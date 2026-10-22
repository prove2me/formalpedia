-- Prove2me | solution 1 for SuReturns.PartialRefunds.corollary1_partial_beats_full
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:25:30.944821+00:00
-- url     : https://prove2.me/submissions/86edc6a3-d49c-45c0-a558-fda6ff8ec616

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


lemma sr_L2 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable (fun v => v) ν) (s p : ℝ) :
    (p - s) * keepProb ν p ≤ reservationPrice ν s - s := by
  unfold keepProb reservationPrice
  have hint : Integrable (fun v => max v s) ν := hν.sup (integrable_const s)
  have hind : Integrable (fun v : ℝ => (p - s) * (Set.Ici p).indicator (fun _ => (1 : ℝ)) v) ν :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
  have h1 : ∫ v, (p - s) * (Set.Ici p).indicator (fun _ => (1 : ℝ)) v ∂ν ≤
      ∫ v, (max v s - s) ∂ν := by
    refine integral_mono hind (hint.sub (integrable_const s)) (fun v => ?_)
    by_cases h : p ≤ v
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 h)]
      have := le_max_left v s
      linarith
    · rw [Set.indicator_of_notMem (by simpa using h), mul_zero]
      have := le_max_right v s
      linarith
  rw [integral_const_mul, integral_indicator_const _ measurableSet_Ici, integral_sub hint (integrable_const s)] at h1
  simpa [Measure.real] using h1

lemma sr_L3 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable (fun v => v) ν) (s : ℝ) :
    meanValuation ν ≤ reservationPrice ν s := by
  unfold meanValuation reservationPrice
  exact integral_mono hν (hν.sup (integrable_const s)) (fun v => le_max_left v s)

lemma sr_L1 (ν D : Measure ℝ) [IsProbabilityMeasure ν] (c s q : ℝ) :
    profit ν D c s (reservationPrice ν s) q s =
      (reservationPrice ν s - s) * expSales D q - (c - s) * q := by
  unfold profit sales
  rw [if_pos le_rfl, sr_ret]
  ring

lemma sr_L4 (D : Measure ℝ) [IsProbabilityMeasure D] (hD0 : D (Set.Iio 0) = 0) (c s M qs : ℝ)
    (hM : 0 < M) (hq : 1 - cdf D qs = (c - s) / M) (q : ℝ) :
    M * expSales D q - (c - s) * q ≤ M * expSales D qs - (c - s) * qs := by
  have hms : M * (1 - cdf D qs) = c - s := by
    have key : ∀ M : ℝ, 0 < M → M * ((c - s) / M) = c - s := fun M hM => by field_simp
    rw [hq]; exact key _ hM
  have h2 := sr_supergrad D hD0 q qs
  have h3 : M * (expSales D q - expSales D qs) ≤ (q - qs) * (c - s) := by
    calc M * (expSales D q - expSales D qs) ≤ M * ((q - qs) * (1 - cdf D qs)) :=
          mul_le_mul_of_nonneg_left h2 hM.le
      _ = (q - qs) * (c - s) := by rw [← hms]; ring
  nlinarith [h3]

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (pF qF : ℝ) (hp : IsMaxOn (fun p => (p - s) * keepProb ν p) Set.univ pF)
    (hqF : 1 - cdf D qF = (c - s) / ((pF - s) * keepProb ν pF))
    (qP : ℝ) (hqP : 1 - cdf D qP = (c - s) / (reservationPrice ν s - s)) :
    (∀ p q, 0 ≤ q →
        fullRefundProfit ν D c s p q ≤ profit ν D c s (reservationPrice ν s) qP s) ∧
      (StrictMonoOn (cdf D) (Set.Ici 0) → qF ≤ qP) := by
  have hρ : c < reservationPrice ν s := lt_of_lt_of_le hcμ (sr_L3 ν hν s)
  have hρs : 0 < reservationPrice ν s - s := by linarith
  have hcs : 0 < c - s := by linarith
  refine ⟨fun p q hq0 => ?_, fun hmono => ?_⟩
  · rw [sr_profit ν D c s p q, sr_L1 ν D c s qP]
    have h1 : ((p - s) * keepProb ν p) * expSales D q ≤ (reservationPrice ν s - s) * expSales D q :=
      mul_le_mul_of_nonneg_right (sr_L2 ν hν s p) (sr_sales_nonneg D hD0 q hq0)
    have h2 := sr_L4 D hD0 c s _ qP hρs hqP q
    linarith
  · obtain ⟨p1, hp1, hk1⟩ := sr_pos ν hν c s hsc hcμ
    have hmspos : 0 < (pF - s) * keepProb ν pF :=
      lt_of_lt_of_le (mul_pos (sub_pos.2 hp1) hk1) (isMaxOn_univ_iff.1 hp p1)
    have hmsle : (pF - s) * keepProb ν pF ≤ reservationPrice ν s - s :=
      sr_L2 ν hν s pF
    have hfrac : (c - s) / (reservationPrice ν s - s) ≤ (c - s) / ((pF - s) * keepProb ν pF) :=
      div_le_div_of_nonneg_left hcs.le hmspos hmsle
    have hcdf : cdf D qF ≤ cdf D qP := by
      rw [← hqF] at hfrac
      rw [← hqP] at hfrac
      linarith
    have hlt1 : (c - s) / (reservationPrice ν s - s) < 1 := by
      rw [div_lt_one hρs]; linarith
    have hpos : 0 < cdf D qP := by
      rw [← hqP] at hlt1; linarith
    have hqP0 : 0 ≤ qP := by
      by_contra hneg
      push_neg at hneg
      have hz : D (Set.Iic qP) = 0 :=
        measure_mono_null (fun x hx => lt_of_le_of_lt (Set.mem_Iic.1 hx) hneg) hD0
      rw [cdf_eq_real] at hpos
      simp [Measure.real, hz] at hpos
    by_contra hlt
    push_neg at hlt
    have := hmono (Set.mem_Ici.2 hqP0) (Set.mem_Ici.2 (hqP0.trans hlt.le)) hlt
    linarith
