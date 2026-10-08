-- Prove2me | solution 1 for SuReturns.Coordination.prop3_proof_retailer_optimum
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:52:50.653144+00:00
-- url     : https://prove2.me/submissions/7e08e463-05b7-4615-affb-306688380c90

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory SuReturns.Coordination SuReturns.PartialRefunds

private lemma max_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (r : ℝ) : Integrable (fun v => max v r) ν := by
  have he : ((fun v : ℝ => v) ⊔ (fun _ => r)) = (fun v => max v r) := by
    funext v
    exact le_antisymm (sup_le (le_max_left v r) (le_max_right v r))
      (max_le le_sup_left le_sup_right)
  rw [← he]
  exact hν.sup (integrable_const r)

private lemma probs_sum (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℝ) :
    keepProb ν r + returnProb ν r = 1 := by
  unfold keepProb returnProb
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [← measure_union (Set.disjoint_left.mpr (by
    intro x hx hy
    exact (not_lt_of_ge (show r ≤ x from hx)) (show x < r from hy))) measurableSet_Iio]
  simp [Set.Ici_union_Iio]

private lemma margin_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (b r : ℝ) :
    reservationPrice ν r - b + (b-r)*returnProb ν r ≤ reservationPrice ν b - b := by
  have hi : Integrable ((Set.Iio r).indicator (fun _ : ℝ => b-r)) ν :=
    (integrable_const (b-r)).indicator measurableSet_Iio
  have hm : Integrable (fun v => max v r-b) ν := by
    simpa only [Pi.sub_def] using (max_integrable ν hν r).sub (integrable_const b)
  have hb : Integrable (fun v => max v b-b) ν := by
    simpa only [Pi.sub_def] using (max_integrable ν hν b).sub (integrable_const b)
  have hle : ∫ v, (max v r - b) + (Set.Iio r).indicator (fun _ : ℝ => b-r) v ∂ν ≤
      ∫ v, max v b - b ∂ν := by
    apply integral_mono (by simpa only [Pi.add_def] using hm.add hi) hb
    intro v
    change max v r - b + (Set.Iio r).indicator (fun _ : ℝ => b-r) v ≤ max v b-b
    by_cases hv : v < r
    · rw [Set.indicator_of_mem (show v ∈ Set.Iio r from hv), max_eq_right hv.le]
      linarith [le_max_right v b]
    · rw [Set.indicator_of_notMem (show v ∉ Set.Iio r from hv), max_eq_left (le_of_not_gt hv), add_zero]
      exact sub_le_sub_right (le_max_left v b) b
  rw [integral_add hm hi, integral_sub (max_integrable ν hν r) (integrable_const b),
    integral_sub (max_integrable ν hν b) (integrable_const b)] at hle
  simpa [integral_indicator measurableSet_Iio, integral_const, reservationPrice,
    returnProb, measureReal_def, mul_comm] using hle

private lemma min_integrable (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : ∀ᵐ d ∂D, 0 ≤ d) (q : ℝ) : Integrable (fun d => min q d) D := by
  apply (integrable_const |q|).mono' (by fun_prop)
  filter_upwards [hD] with d hd
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_min (neg_abs_le q) (le_trans (neg_nonpos.mpr (abs_nonneg q)) hd)
  · exact le_trans (min_le_left q d) (le_abs_self q)

private lemma sales_support (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : ∀ᵐ d ∂D, 0 ≤ d) (q qs : ℝ) :
    SupplyChainTheory.expSales D q - SupplyChainTheory.expSales D qs ≤
      (q-qs) * (1-cdf D qs) := by
  have hi : Integrable ((Set.Ioi qs).indicator (fun _ : ℝ => q-qs)) D :=
    (integrable_const _).indicator measurableSet_Ioi
  have hm := (min_integrable D hD q).sub (min_integrable D hD qs)
  have hh : ∫ d, min q d - min qs d ∂D ≤
      ∫ d, (Set.Ioi qs).indicator (fun _ : ℝ => q-qs) d ∂D := by
    apply integral_mono hm hi
    intro d
    change min q d - min qs d ≤ (Set.Ioi qs).indicator (fun _ : ℝ => q-qs) d
    by_cases hd : qs < d
    · rw [Set.indicator_of_mem (show d ∈ Set.Ioi qs from hd), min_eq_left hd.le]
      linarith [min_le_left q d]
    · rw [Set.indicator_of_notMem (show d ∉ Set.Ioi qs from hd), min_eq_right (le_of_not_gt hd)]
      linarith [min_le_right q d]
  rw [integral_sub (min_integrable D hD q) (min_integrable D hD qs)] at hh
  have ht : D.real (Set.Ioi qs) = 1-cdf D qs := by
    rw [cdf_eq_real, ← Set.compl_Iic, measureReal_compl measurableSet_Iic]
    simp
  simpa [SupplyChainTheory.expSales, integral_indicator measurableSet_Ioi,
    integral_const, ← measureReal_def, ht, mul_comm] using hh

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (w b l qstar : ℝ) (hpos : 0 < SuReturns.PartialRefunds.reservationPrice ν (b - l) - b)
    (hq : 1 - cdf D qstar = (w - b) / (SuReturns.PartialRefunds.reservationPrice ν (b - l) - b)) :
    ∀ p r q : ℝ, 0 ≤ q →
      retailerDiffBuyback ν D w b l p q r ≤
        retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν (b - l)) qstar (b - l) := by
  intro p r q hq0
  have hD : ∀ᵐ d ∂D, 0 ≤ d := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using hD0
  have hs : 0 ≤ SupplyChainTheory.expSales D q := by
    apply integral_nonneg_of_ae
    filter_upwards [hD] with d hd
    exact le_min hq0 hd
  have hm := margin_bound ν hν (b-l) r
  have hpr := probs_sum ν r
  have hpb := probs_sum ν (b-l)
  have hfract : (reservationPrice ν (b-l)-b) * (1-cdf D qstar) = w-b := by
    rw [hq]
    field_simp
  have hnews := mul_le_mul_of_nonneg_left (sales_support D hD q qstar) hpos.le
  rw [show (reservationPrice ν (b-l)-b) * ((q-qstar)*(1-cdf D qstar)) =
    (q-qstar)*(w-b) by rw [mul_left_comm, hfract]] at hnews
  have hopt : (reservationPrice ν (b-l)-b) * SupplyChainTheory.expSales D q - (w-b)*q ≤
      (reservationPrice ν (b-l)-b) * SupplyChainTheory.expSales D qstar - (w-b)*qstar := by
    nlinarith [hfract]
  have hb : (reservationPrice ν (b-l)-b)*keepProb ν (b-l) +
      (reservationPrice ν (b-l)-(b-l)-l)*returnProb ν (b-l) = reservationPrice ν (b-l)-b := by
    nlinarith [hpb]
  unfold retailerDiffBuyback sales
  rw [if_pos le_rfl, hb]
  split_ifs with hp
  · have hr : (p-b)*keepProb ν r + (p-r-l)*returnProb ν r ≤ reservationPrice ν (b-l)-b := by
      rw [show keepProb ν r = 1-returnProb ν r by linarith]
      nlinarith [hm]
    exact le_trans (sub_le_sub_right (mul_le_mul_of_nonneg_right hr hs) _) hopt
  · simp only [mul_zero]
    exact le_trans (sub_le_sub_right (mul_nonneg hpos.le hs) _) hopt

#print axioms solution
