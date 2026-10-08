-- Prove2me | solution 1 for SuReturns.PartialRefunds.prop2_first_step
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:36:19.206999+00:00
-- url     : https://prove2.me/submissions/91671842-ab07-4fc2-9601-0ae0e9c40af3

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model
open MeasureTheory ProbabilityTheory SuReturns.PartialRefunds

private theorem partition (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℝ) :
    keepProb ν r + returnProb ν r = 1 := by
  unfold keepProb returnProb
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [← measure_union (Set.disjoint_left.mpr (by
    intro x hx hy
    exact (not_lt_of_ge (show r ≤ x from hx)) (show x < r from hy))) measurableSet_Iio]
  simp [Set.Ici_union_Iio]

private theorem price_decomp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (a r : ℝ) :
    reservationPrice ν r = (∫ v in Set.Ici r, (v-a) ∂ν) + (a-r)*keepProb ν r + r := by
  classical
  let g := (Set.Ici r).indicator (fun v : ℝ => v-a)
  let k := (Set.Ici r).indicator (fun _ : ℝ => (1 : ℝ))
  have hg : Integrable g ν := (hν.sub (integrable_const a)).indicator measurableSet_Ici
  have hk : Integrable k ν := (integrable_const (1 : ℝ)).indicator measurableSet_Ici
  have hkint : (∫ v, k v ∂ν) = keepProb ν r := by
    simp [k, integral_indicator_const, keepProb, Measure.real]
  have hfun : (fun v : ℝ => max v r) = (fun v => g v + (a-r)*k v+r) := by
    funext v
    by_cases hv : r ≤ v
    · simp [g, k, hv]
    · simp [g, k, hv, max_eq_right (le_of_not_ge hv)]
  unfold reservationPrice
  rw [hfun, integral_add (show Integrable (fun v => g v + (a-r)*k v) ν from hg.add (hk.const_mul (a-r))) (integrable_const r),
    integral_add hg (hk.const_mul (a-r)), integral_const_mul, hkint]
  simp [g, integral_indicator measurableSet_Ici]

private theorem margin_identity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s r : ℝ) :
    margin ν s (reservationPrice ν r) r = ∫ v in Set.Ici r, (v-s) ∂ν := by
  have hp := partition ν r
  have hd := price_decomp ν hν s r
  unfold margin
  rw [hd]
  nlinarith [congrArg (fun z : ℝ => z * ((∫ v in Set.Ici r, (v-s) ∂ν) + (s-r)*keepProb ν r)) hp]

private theorem refund_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s r : ℝ) :
    ∫ v in Set.Ici r, (v-s) ∂ν ≤ ∫ v in Set.Ici s, (v-s) ∂ν := by
  rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Ici]
  apply integral_mono ((hν.sub (integrable_const s)).indicator measurableSet_Ici)
    ((hν.sub (integrable_const s)).indicator measurableSet_Ici)
  intro v
  by_cases hr : r ≤ v <;> by_cases hs : s ≤ v
  · simp [Set.indicator_of_mem, hr, hs]
  · simp [hr, hs]; linarith
  · simp [hr, hs]
  · simp [hr, hs]

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s : ℝ) :
    ∀ p r, p ≤ reservationPrice ν r → margin ν s p r ≤ margin ν s (reservationPrice ν s) s := by
  intro p r hp
  calc
    margin ν s p r ≤ margin ν s (reservationPrice ν r) r := by
      unfold margin
      exact add_le_add (mul_le_mul_of_nonneg_right (sub_le_sub_right hp s) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hp r) ENNReal.toReal_nonneg)
    _ = ∫ v in Set.Ici r, (v-s) ∂ν := margin_identity ν hν s r
    _ ≤ ∫ v in Set.Ici s, (v-s) ∂ν := refund_bound ν hν s r
    _ = margin ν s (reservationPrice ν s) s := (margin_identity ν hν s s).symm

#print axioms solution
