-- Prove2me | solution 1 for SuReturnsAudit.OptimalPolicy.proposition2_complete_optimal_policy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T14:17:28.378881+00:00
-- url     : https://prove2.me/submissions/e88f8570-b385-4a88-b8c3-9f12ef58d215

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace SuRet4abd

open SuReturns.PartialRefunds

lemma integrable_max (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable (fun v => v) ν)
    (r : ℝ) : Integrable (fun v => max v r) ν := by
  refine Integrable.mono' (hν.norm.add (integrable_const |r|))
    (measurable_id.max measurable_const).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  have h1 := le_abs_self v; have h2 := neg_abs_le v
  have h3 := le_abs_self r; have h4 := neg_abs_le r
  rw [abs_le]; constructor
  · have := le_max_left v r; linarith
  · exact max_le (by linarith) (by linarith)

lemma kg (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℝ) :
    keepProb ν r + returnProb ν r = 1 := by
  unfold keepProb returnProb
  have h := prob_compl_eq_one_sub (μ := ν) (measurableSet_Ici (a := r))
  rw [Set.compl_Ici] at h
  rw [h, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]; ring

lemma key (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable (fun v => v) ν) (r s : ℝ) :
    reservationPrice ν r - (r - s) * returnProb ν r ≤ reservationPrice ν s := by
  have hm : MeasurableSet (Set.Iio r) := measurableSet_Iio
  have hI : Integrable (fun v => (Set.Iio r).indicator (fun _ => (1:ℝ)) v) ν :=
    (integrable_const (1:ℝ)).indicator hm
  have hG : returnProb ν r = ∫ v, (Set.Iio r).indicator (fun _ => (1:ℝ)) v ∂ν := by
    rw [integral_indicator_const _ hm]; simp [returnProb, measureReal_def]
  unfold reservationPrice
  rw [hG, ← integral_const_mul, ← integral_sub (integrable_max ν hν r) (hI.const_mul _)]
  refine integral_mono ((integrable_max ν hν r).sub (hI.const_mul _)) (integrable_max ν hν s)
    (fun v => ?_)
  dsimp only
  simp only [Set.indicator, Set.mem_Iio]
  split_ifs with h
  · rw [max_eq_right h.le]; linarith [le_max_right v s]
  · rw [max_eq_left (not_lt.mp h)]; linarith [le_max_left v s]

lemma intmin (D : Measure ℝ) [IsProbabilityMeasure D] (hpos : ∀ᵐ d ∂D, 0 ≤ d) (q : ℝ) :
    Integrable (fun d => min q d) D := by
  refine Integrable.mono' (integrable_const |q|)
    (measurable_const.min measurable_id).aestronglyMeasurable ?_
  filter_upwards [hpos] with d hd
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rcases le_total q d with h | h
    · rw [min_eq_left h]; exact neg_abs_le q
    · rw [min_eq_right h]; linarith [abs_nonneg q]
  · exact (min_le_left q d).trans (le_abs_self q)

lemma expSales_nonneg (D : Measure ℝ) (hpos : ∀ᵐ d ∂D, 0 ≤ d) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ SupplyChainTheory.expSales D q := by
  unfold SupplyChainTheory.expSales
  refine integral_nonneg_of_ae ?_
  filter_upwards [hpos] with d hd
  exact le_min hq hd

lemma newsvendor (D : Measure ℝ) [IsProbabilityMeasure D] (hpos : ∀ᵐ d ∂D, 0 ≤ d)
    (q q0 : ℝ) :
    SupplyChainTheory.expSales D q - SupplyChainTheory.expSales D q0
      ≤ (q - q0) * (1 - cdf D q0) := by
  have hm : MeasurableSet (Set.Ioi q0) := measurableSet_Ioi
  have hI : Integrable (fun d => (Set.Ioi q0).indicator (fun _ => (1:ℝ)) d) D :=
    (integrable_const (1:ℝ)).indicator hm
  have hF : 1 - cdf D q0 = ∫ d, (Set.Ioi q0).indicator (fun _ => (1:ℝ)) d ∂D := by
    rw [integral_indicator_const _ hm, cdf_eq_real]
    have h := prob_compl_eq_one_sub (μ := D) (measurableSet_Iic (a := q0))
    rw [Set.compl_Iic] at h
    simp only [measureReal_def, h, smul_eq_mul, mul_one]
    rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  unfold SupplyChainTheory.expSales
  rw [hF, ← integral_const_mul, ← integral_sub (intmin D hpos q) (intmin D hpos q0)]
  refine integral_mono ((intmin D hpos q).sub (intmin D hpos q0)) (hI.const_mul _)
    (fun d => ?_)
  dsimp only
  simp only [Set.indicator, Set.mem_Ioi]
  split_ifs with h
  · rw [min_eq_left h.le]; linarith [min_le_left q d]
  · push_neg at h
    rw [min_eq_right h]
    rcases le_total q d with h2 | h2
    · rw [min_eq_left h2]; linarith
    · rw [min_eq_right h2]; linarith

lemma newsvendor2 (D : Measure ℝ) [IsProbabilityMeasure D] (hpos : ∀ᵐ d ∂D, 0 ≤ d)
    (q q0 : ℝ) :
    SupplyChainTheory.expSales D q - SupplyChainTheory.expSales D q0
      ≤ (q - q0) * (D (Set.Ici q0)).toReal := by
  have hm : MeasurableSet (Set.Ici q0) := measurableSet_Ici
  have hI : Integrable (fun d => (Set.Ici q0).indicator (fun _ => (1:ℝ)) d) D :=
    (integrable_const (1:ℝ)).indicator hm
  have hF : (D (Set.Ici q0)).toReal = ∫ d, (Set.Ici q0).indicator (fun _ => (1:ℝ)) d ∂D := by
    rw [integral_indicator_const _ hm]; simp [measureReal_def]
  unfold SupplyChainTheory.expSales
  rw [hF, ← integral_const_mul, ← integral_sub (intmin D hpos q) (intmin D hpos q0)]
  refine integral_mono ((intmin D hpos q).sub (intmin D hpos q0)) (hI.const_mul _)
    (fun d => ?_)
  dsimp only
  simp only [Set.indicator, Set.mem_Ici]
  split_ifs with h
  · rw [min_eq_left h]; linarith [min_le_left q d]
  · push_neg at h
    rw [min_eq_right h.le]; linarith [min_le_right q d]

lemma tail_Ioi (D : Measure ℝ) [IsProbabilityMeasure D] (q : ℝ) :
    (D (Set.Ioi q)).toReal = 1 - cdf D q := by
  rw [cdf_eq_real]
  have h := prob_compl_eq_one_sub (μ := D) (measurableSet_Iic (a := q))
  rw [Set.compl_Iic] at h
  rw [h, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    measureReal_def]

lemma exists_quantile (D : Measure ℝ) [IsProbabilityMeasure D] (hD0 : D (Set.Iio 0) = 0)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ qstar : ℝ, 0 ≤ qstar ∧
      (D (Set.Ioi qstar)).toReal ≤ α ∧ α ≤ (D (Set.Ici qstar)).toReal := by
  set S := {q : ℝ | 1 - α ≤ cdf D q} with hS
  have hne : S.Nonempty := by
    have h := (tendsto_cdf_atTop D).eventually (lt_mem_nhds (by linarith : 1 - α < 1))
    obtain ⟨q, hq⟩ := h.exists
    exact ⟨q, le_of_lt hq⟩
  have hlow : ∀ q ∈ S, 0 ≤ q := by
    intro q hq
    by_contra hneg
    push_neg at hneg
    have h0 : cdf D q = 0 := by
      rw [cdf_eq_real]
      have : D (Set.Iic q) = 0 := measure_mono_null (Set.Iic_subset_Iio.2 hneg) hD0
      simp [measureReal_def, this]
    have hq' : 1 - α ≤ cdf D q := hq
    linarith
  have hbdd : BddBelow S := ⟨0, hlow⟩
  have hq0nn : 0 ≤ sInf S := le_csInf hne hlow
  have hmem : 1 - α ≤ cdf D (sInf S) := by
    have hc : Tendsto (cdf D) (𝓝[>] (sInf S)) (𝓝 (cdf D (sInf S))) :=
      ((cdf D).right_continuous (sInf S)).tendsto.mono_left
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    refine ge_of_tendsto hc ?_
    refine eventually_nhdsWithin_of_forall (fun x hx => ?_)
    obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hne hx
    have hy : 1 - α ≤ cdf D y := hyS
    exact le_trans hy ((cdf D).mono hyx.le)
  have hleft : Function.leftLim (cdf D) (sInf S) ≤ 1 - α := by
    refine le_of_tendsto ((cdf D).mono.tendsto_leftLim (sInf S)) ?_
    refine eventually_nhdsWithin_of_forall (fun x hx => ?_)
    by_contra h
    push_neg at h
    have hxS : x ∈ S := le_of_lt h
    have : sInf S ≤ x := csInf_le hbdd hxS
    exact absurd (Set.mem_Iio.1 hx) (not_lt.2 this)
  refine ⟨sInf S, hq0nn, ?_, ?_⟩
  · rw [tail_Ioi]; linarith
  · have hI : D (Set.Ici (sInf S)) = ENNReal.ofReal (1 - Function.leftLim (cdf D) (sInf S)) := by
      calc D (Set.Ici (sInf S)) = (cdf D).measure (Set.Ici (sInf S)) := by
            rw [measure_cdf (μ := D)]
        _ = _ := StieltjesFunction.measure_Ici _ (tendsto_cdf_atTop D) (sInf S)
    rw [hI, ENNReal.toReal_ofReal (by linarith)]
    linarith

end SuRet4abd

open MeasureTheory ProbabilityTheory SuReturns.PartialRefunds in
theorem solution (ν D : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure D]
    (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν) :
    let pstar := reservationPrice ν s
    let rstar := s
    let α := (c - s) / (pstar - s)
    (0 ≤ rstar ∧ rstar < pstar) ∧ (0 < α ∧ α < 1) ∧
    (∃ qstar : ℝ, 0 ≤ qstar ∧
      (D (Set.Ioi qstar)).toReal ≤ α ∧ α ≤ (D (Set.Ici qstar)).toReal) ∧
    (∀ qstar : ℝ, 0 ≤ qstar →
      (D (Set.Ioi qstar)).toReal ≤ α → α ≤ (D (Set.Ici qstar)).toReal →
      (∀ p q r : ℝ, 0 ≤ q →
        profit ν D c s p q r ≤ profit ν D c s pstar qstar rstar) ∧
      (D {qstar} = 0 →
        1 - cdf D qstar = (c - s) / (pstar - s) ∧
        (c - s) / (pstar - s) = (c - s) / (reservationPrice ν s - s))) := by
  dsimp only
  set R := SuReturns.PartialRefunds.reservationPrice ν s with hR
  set α := (c - s) / (R - s) with hα
  have hpos : ∀ᵐ d ∂D, 0 ≤ d := by
    refine ae_iff.2 (measure_mono_null (fun d hd => ?_) hD0)
    simp only [Set.mem_setOf_eq, not_le] at hd
    exact hd
  have hRμ : SuReturns.PartialRefunds.meanValuation ν ≤ R := by
    rw [hR]
    exact integral_mono hν (SuRet4abd.integrable_max ν hν s) (fun v => le_max_left v s)
  have hRs : 0 < R - s := by linarith
  have hcs : 0 < c - s := by linarith
  have hα0 : 0 < α := by rw [hα]; exact div_pos hcs hRs
  have hα1 : α < 1 := by rw [hα, div_lt_one hRs]; linarith
  have hαe : c - s = α * (R - s) := by rw [hα, div_mul_cancel₀ _ hRs.ne']
  refine ⟨⟨hs, by linarith⟩, ⟨hα0, hα1⟩, SuRet4abd.exists_quantile D hD0 α hα0 hα1, ?_⟩
  intro qstar hq0 hlo hhi
  refine ⟨?_, ?_⟩
  · intro p q r hq
    have hopt : SuReturns.PartialRefunds.profit ν D c s R qstar s
        = (R - s) * SupplyChainTheory.expSales D qstar - (c - s) * qstar := by
      have hk := SuRet4abd.kg ν s
      unfold SuReturns.PartialRefunds.profit SuReturns.PartialRefunds.sales
      rw [if_pos le_rfl]
      linear_combination (R * SupplyChainTheory.expSales D qstar) * hk
    have hE := SuRet4abd.expSales_nonneg D hpos q hq
    have h1 : SuReturns.PartialRefunds.profit ν D c s p q r
        ≤ (R - s) * SupplyChainTheory.expSales D q - (c - s) * q := by
      have hk : SuReturns.PartialRefunds.keepProb ν r
          = 1 - SuReturns.PartialRefunds.returnProb ν r := by
        linarith [SuRet4abd.kg ν r]
      unfold SuReturns.PartialRefunds.profit SuReturns.PartialRefunds.sales
      rw [hk]
      split_ifs with hp
      · have hkey : SuReturns.PartialRefunds.reservationPrice ν r
            - (r - s) * SuReturns.PartialRefunds.returnProb ν r ≤ R :=
          SuRet4abd.key ν hν r s
        have hb' : p - s - (r - s) * SuReturns.PartialRefunds.returnProb ν r ≤ R - s := by
          linarith
        have e : p * (1 - SuReturns.PartialRefunds.returnProb ν r)
              * SupplyChainTheory.expSales D q
            + (p - r + s) * SuReturns.PartialRefunds.returnProb ν r
              * SupplyChainTheory.expSales D q
            + s * (q - SupplyChainTheory.expSales D q) - c * q
            = (p - s - (r - s) * SuReturns.PartialRefunds.returnProb ν r)
              * SupplyChainTheory.expSales D q - (c - s) * q := by ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_right hb' hE]
      · nlinarith [mul_nonneg hRs.le hE]
    have h2 : SupplyChainTheory.expSales D q - SupplyChainTheory.expSales D qstar
        ≤ (q - qstar) * α := by
      rcases le_total qstar q with hqq | hqq
      · have h3 := SuRet4abd.newsvendor D hpos q qstar
        rw [← SuRet4abd.tail_Ioi D qstar] at h3
        nlinarith [mul_le_mul_of_nonneg_left hlo (sub_nonneg.2 hqq)]
      · have h3 := SuRet4abd.newsvendor2 D hpos q qstar
        nlinarith [mul_le_mul_of_nonpos_left hhi (sub_nonpos.2 hqq)]
    have h4 := mul_le_mul_of_nonneg_left h2 hRs.le
    have h5 : (R - s) * ((q - qstar) * α) = (c - s) * (q - qstar) := by rw [hαe]; ring
    rw [hopt]
    nlinarith
  · intro hsing
    have hle : (D (Set.Ici qstar)).toReal ≤ (D (Set.Ioi qstar)).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      rw [← Set.Ioi_insert, Set.insert_eq]
      calc D ({qstar} ∪ Set.Ioi qstar) ≤ D {qstar} + D (Set.Ioi qstar) := measure_union_le _ _
        _ = D (Set.Ioi qstar) := by rw [hsing, zero_add]
    refine ⟨?_, rfl⟩
    rw [← SuRet4abd.tail_Ioi D qstar]
    linarith
