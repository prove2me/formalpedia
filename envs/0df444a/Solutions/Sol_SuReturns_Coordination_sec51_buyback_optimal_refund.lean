-- Prove2me | solution 1 for SuReturns.Coordination.sec51_buyback_optimal_refund
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:32:58.057533+00:00
-- url     : https://prove2.me/submissions/de06fc59-27f3-4869-b5c3-d08de62ceb38

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

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (w b : ℝ) :
    ∀ p r q : ℝ, 0 ≤ q →
      retailerBuyback ν D w b p q r ≤ retailerBuyback ν D w b (SuReturns.PartialRefunds.reservationPrice ν b) q b := by
  intro p r q hq
  have hs : 0 ≤ SupplyChainTheory.expSales D q := by
    apply integral_nonneg_of_ae
    have hD : ∀ᵐ d ∂D, 0 ≤ d := by
      rw [ae_iff]
      simpa only [not_le, Set.Iio] using hD0
    filter_upwards [hD] with d hd
    exact le_min hq hd
  have hpb := probs_sum ν b
  have hpr := probs_sum ν r
  have hm := margin_bound ν hν b r
  have hnon : 0 ≤ reservationPrice ν b - b := by
    have hh := integral_mono (integrable_const b) (max_integrable ν hν b)
      (fun v => le_max_right v b)
    simpa [reservationPrice] using sub_nonneg.mpr hh
  unfold retailerBuyback sales
  rw [if_pos le_rfl]
  have hb : (reservationPrice ν b-b)*keepProb ν b +
      (reservationPrice ν b-b)*returnProb ν b = reservationPrice ν b-b := by
    nlinarith [hpb]
  rw [hb]
  split_ifs with hp
  · have hr : (p-b)*keepProb ν r + (p-r)*returnProb ν r ≤ reservationPrice ν b-b := by
      have he : (p-b)*keepProb ν r + (p-r)*returnProb ν r = p-b+(b-r)*returnProb ν r := by
        rw [show keepProb ν r = 1-returnProb ν r by linarith]
        ring
      rw [he]
      linarith
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right hr hs) _
  · simp only [mul_zero]
    exact sub_le_sub_right (mul_nonneg hnon hs) _

#print axioms solution
