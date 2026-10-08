-- Prove2me | solution 1 for SuReturns.Coordination.sec54_kept_only_rebate_refund
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:47:01.871152+00:00
-- url     : https://prove2.me/submissions/3a425d44-0895-44f2-925a-1686bb0550ee

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory
open SuReturns.Coordination SuReturns.PartialRefunds

private theorem partition (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℝ) :
    keepProb ν r + returnProb ν r = 1 := by
  unfold keepProb returnProb
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [← measure_union (Set.disjoint_left.mpr (by
    intro x hx hy
    exact (not_lt_of_ge (show r ≤ x from hx)) (show x < r from hy))) measurableSet_Iio]
  simp [Set.Ici_union_Iio]

private theorem margin_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (a r p : ℝ) (hp : p ≤ reservationPrice ν r) :
    (p - a) * keepProb ν r + (p - r) * returnProb ν r ≤ reservationPrice ν a - a := by
  classical
  let g := (Set.Ici r).indicator (fun v : ℝ => v - a)
  let k := (Set.Ici r).indicator (fun _ : ℝ => (1 : ℝ))
  have hg : Integrable g ν := (hν.sub (integrable_const a)).indicator measurableSet_Ici
  have hk : Integrable k ν := (integrable_const (1 : ℝ)).indicator measurableSet_Ici
  have hkint : (∫ v, k v ∂ν) = keepProb ν r := by
    simp [k, integral_indicator_const, keepProb, Measure.real]
  have hfun : (fun v : ℝ => max v r) = (fun v => g v + (a - r) * k v + r) := by
    funext v
    by_cases hv : r ≤ v
    · simp [g, k, hv]
    · simp [g, k, hv, max_eq_right (le_of_not_ge hv)]
  have hres : reservationPrice ν r = (∫ v, g v ∂ν) + (a-r) * keepProb ν r + r := by
    unfold reservationPrice
    rw [hfun, integral_add (show Integrable (fun v => g v + (a-r)*k v) ν from hg.add (hk.const_mul (a-r))) (integrable_const r),
      integral_add hg (hk.const_mul (a-r)), integral_const_mul, hkint]
    simp
  have hle : (∫ v, g v ∂ν) ≤ reservationPrice ν a - a := by
    have hm := integral_mono hg (show Integrable (fun v => max v a - a) ν from (hν.sup (integrable_const a)).sub (integrable_const a))
      (fun v => show g v ≤ max v a - a from by
        by_cases hv : r ≤ v
        · simp [g, hv]
        · simp [g, hv])
    rw [integral_sub (show Integrable (fun v => max v a) ν from hν.sup (integrable_const a)) (integrable_const a)] at hm
    simpa [reservationPrice] using hm
  have hprob := partition ν r
  have hk0 : 0 ≤ keepProb ν r := ENNReal.toReal_nonneg
  have hr0 : 0 ≤ returnProb ν r := ENNReal.toReal_nonneg
  calc
    (p-a)*keepProb ν r + (p-r)*returnProb ν r
        ≤ (reservationPrice ν r-a)*keepProb ν r + (reservationPrice ν r-r)*returnProb ν r :=
      add_le_add (mul_le_mul_of_nonneg_right (sub_le_sub_right hp a) hk0)
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hp r) hr0)
    _ = ∫ v, g v ∂ν := by
      rw [hres]
      nlinarith [congrArg (fun z : ℝ => z * ((∫ v, g v ∂ν) + (a-r)*keepProb ν r)) hprob]
    _ ≤ reservationPrice ν a - a := hle

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (s w u : ℝ) (hu : 0 < u) :
    (∀ p r q : ℝ, 0 ≤ q →
        retailerKeptRebate ν D s w u p q r ≤
          retailerKeptRebate ν D s w u (reservationPrice ν (s - u)) q (s - u)) ∧
      s - u < s := by
  constructor
  · intro p r q hq
    have hs0 : 0 ≤ SupplyChainTheory.expSales D q := by
      apply integral_nonneg_of_ae
      have hd : ∀ᵐ d ∂D, 0 ≤ d := by
        rw [ae_iff]
        convert hD0 using 2
        ext d
        simp
      filter_upwards [hd] with d hd
      exact le_min hq hd
    have hbest : 0 ≤ reservationPrice ν (s-u) - (s-u) := by
      have hm := integral_mono (integrable_const (s-u)) (hν.sup (integrable_const (s-u)))
        (fun v => le_max_right v (s-u))
      simpa [reservationPrice] using sub_nonneg.mpr hm
    have hprob := partition ν (s-u)
    unfold retailerKeptRebate sales
    rw [if_pos le_rfl]
    have he : (reservationPrice ν (s-u)-s+u)*keepProb ν (s-u) +
        (reservationPrice ν (s-u)-(s-u))*returnProb ν (s-u) =
        reservationPrice ν (s-u) - (s-u) := by
      nlinarith [congrArg (fun z : ℝ => z * (reservationPrice ν (s-u)-(s-u))) hprob]
    rw [he]
    split_ifs with hp
    · have hm := margin_bound ν hν (s-u) r p hp
      have hh := mul_le_mul_of_nonneg_right hm hs0
      nlinarith
    · have hh := mul_nonneg hbest hs0
      nlinarith
  · linarith

#print axioms solution
