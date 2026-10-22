-- Prove2me | solution 1 for SuReturns.Coordination.proposition3_differentiated_buyback
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T06:11:49.237343+00:00
-- url     : https://prove2.me/submissions/dc3259fd-ed10-4577-867e-a5bbd174cdb0

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace SuRetB591

open SuReturns.PartialRefunds SuReturns.Coordination

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

end SuRetB591

open MeasureTheory ProbabilityTheory SuReturns.Coordination in
theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < SuReturns.PartialRefunds.meanValuation ν)
    (qSC : ℝ) (hqSC : 1 - cdf D qSC = (c - s) / (SuReturns.PartialRefunds.reservationPrice ν s - s))
    (φ w b l : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hw : w = φ * c + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hb : b = φ * s + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hl : b - l = s) :
    (∀ p r q : ℝ, 0 ≤ q →
        retailerDiffBuyback ν D w b l p q r ≤
          retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν s) qSC s) ∧
      retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν s) qSC s =
        φ * chainProfit ν D c s (SuReturns.PartialRefunds.reservationPrice ν s) qSC s ∧
      b ≤ w ∧ 0 ≤ l ∧ s ≤ b - l := by
  set R := SuReturns.PartialRefunds.reservationPrice ν s with hR
  have hpos : ∀ᵐ d ∂D, 0 ≤ d := by
    refine ae_iff.2 (measure_mono_null (fun d hd => ?_) hD0)
    simp only [Set.mem_setOf_eq, not_le] at hd
    exact hd
  have hRμ : SuReturns.PartialRefunds.meanValuation ν ≤ R := by
    rw [hR]
    exact integral_mono hν (SuRetB591.integrable_max ν hν s) (fun v => le_max_left v s)
  have hRs : 0 < R - s := by linarith
  -- profit identity
  have hl' : l = b - s := by linarith
  have ident : ∀ p q r : ℝ, retailerDiffBuyback ν D w b l p q r
      = φ * chainProfit ν D c s p q r
        + (1 - φ) * (SuReturns.PartialRefunds.sales ν D p q r
          * (p - R - (r - s) * SuReturns.PartialRefunds.returnProb ν r)) := by
    intro p q r
    have hk : SuReturns.PartialRefunds.keepProb ν r = 1 - SuReturns.PartialRefunds.returnProb ν r := by
      linarith [SuRetB591.kg ν r]
    unfold retailerDiffBuyback chainProfit
    rw [hk, hl', hb, hw]; ring
  -- chain profit at the SC point
  have hSC : chainProfit ν D c s R qSC s
      = (R - s) * SupplyChainTheory.expSales D qSC - (c - s) * qSC := by
    have hk : SuReturns.PartialRefunds.keepProb ν s = 1 - SuReturns.PartialRefunds.returnProb ν s := by
      linarith [SuRetB591.kg ν s]
    unfold chainProfit SuReturns.PartialRefunds.sales
    rw [if_pos le_rfl, hk]; ring
  have hRet : retailerDiffBuyback ν D w b l R qSC s = φ * chainProfit ν D c s R qSC s := by
    rw [ident]; ring
  -- chain bound
  have hchain : ∀ p q r : ℝ, 0 ≤ q → chainProfit ν D c s p q r ≤ chainProfit ν D c s R qSC s := by
    intro p q r hq
    have hE := SuRetB591.expSales_nonneg D hpos q hq
    have h1 : chainProfit ν D c s p q r
        ≤ (R - s) * SupplyChainTheory.expSales D q - (c - s) * q := by
      have hk : SuReturns.PartialRefunds.keepProb ν r = 1 - SuReturns.PartialRefunds.returnProb ν r := by
        linarith [SuRetB591.kg ν r]
      unfold chainProfit SuReturns.PartialRefunds.sales
      rw [hk]
      split_ifs with hp
      · have hkey := SuRetB591.key ν hν r s
        rw [← hR] at hkey
        have hb' : (p - s) * (1 - SuReturns.PartialRefunds.returnProb ν r)
            + (p - r) * SuReturns.PartialRefunds.returnProb ν r ≤ R - s := by
          have : (p - s) * (1 - SuReturns.PartialRefunds.returnProb ν r)
            + (p - r) * SuReturns.PartialRefunds.returnProb ν r
              = p - s - (r - s) * SuReturns.PartialRefunds.returnProb ν r := by ring
          rw [this]; linarith
        nlinarith [mul_le_mul_of_nonneg_right hb' hE]
      · nlinarith [mul_nonneg hRs.le hE]
    have h2 := mul_le_mul_of_nonneg_left (SuRetB591.newsvendor D hpos q qSC) hRs.le
    rw [hqSC] at h2
    have e : (R - s) * ((q - qSC) * ((c - s) / (R - s))) = (q - qSC) * (c - s) := by
      field_simp
    rw [e] at h2
    rw [hSC]
    nlinarith
  -- retailer bound
  have hgap : ∀ p q r : ℝ, 0 ≤ q →
      SuReturns.PartialRefunds.sales ν D p q r
        * (p - R - (r - s) * SuReturns.PartialRefunds.returnProb ν r) ≤ 0 := by
    intro p q r hq
    unfold SuReturns.PartialRefunds.sales
    split_ifs with hp
    · have hkey := SuRetB591.key ν hν r s
      rw [← hR] at hkey
      have hE := SuRetB591.expSales_nonneg D hpos q hq
      exact mul_nonpos_of_nonneg_of_nonpos hE (by linarith)
    · simp
  refine ⟨?_, hRet, ?_, ?_, ?_⟩
  · intro p r q hq
    rw [hRet, ident]
    have := hgap p q r hq
    have := hchain p q r hq
    nlinarith [mul_le_mul_of_nonneg_left (hchain p q r hq) hφ0,
      mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1 - φ) (hgap p q r hq)]
  · rw [hw, hb]; nlinarith
  · rw [hl', hb]; nlinarith
  · linarith
