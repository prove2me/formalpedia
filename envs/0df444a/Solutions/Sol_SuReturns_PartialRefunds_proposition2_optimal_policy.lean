-- Prove2me | solution 1 for SuReturns.PartialRefunds.proposition2_optimal_policy
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:22:07.262348+00:00
-- url     : https://prove2.me/submissions/630db977-9caa-4e4d-bdc4-46048554115a

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

private theorem demand_nonneg (D : Measure ℝ) (hD0 : D (Set.Iio 0) = 0) :
    ∀ᵐ x ∂D, 0 ≤ x := by
  rw [ae_iff]
  simpa only [not_le, Set.Iio] using hD0

private theorem min_integrable (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD0 : D (Set.Iio 0) = 0) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x => min q x) D := by
  apply (integrable_const q).mono' (measurable_const.min measurable_id).aestronglyMeasurable
  filter_upwards [demand_nonneg D hD0] with x hx
  dsimp only [Function.comp_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hq hx)]
  exact min_le_left _ _

private theorem sales_nonneg (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD0 : D (Set.Iio 0) = 0) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ SupplyChainTheory.expSales D q := by
  apply integral_nonneg_of_ae
  filter_upwards [demand_nonneg D hD0] with x hx
  exact le_min hq hx

private theorem tail (D : Measure ℝ) [IsProbabilityMeasure D] (t : ℝ) :
    D.real (Set.Ioi t) = 1 - cdf D t := by
  rw [cdf_eq_real, ← Set.compl_Iic, measureReal_compl measurableSet_Iic]
  simp

private theorem sales_support (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD0 : D (Set.Iio 0) = 0) (q t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) :
    SupplyChainTheory.expSales D q - SupplyChainTheory.expSales D t ≤
      (1 - cdf D t) * (q-t) := by
  have hi := min_integrable D hD0 q hq
  have ht' := min_integrable D hD0 t ht
  let k := (Set.Ioi t).indicator (fun _ : ℝ => (1 : ℝ))
  have hk : Integrable k D := (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hpoint (x : ℝ) : min q x - min t x ≤ k x * (q-t) := by
    by_cases hx : t < x
    · simp only [k, Set.indicator_of_mem (show x ∈ Set.Ioi t from hx), one_mul, min_eq_left hx.le]
      linarith [min_le_left q x]
    · simp only [k, Set.indicator_of_notMem (show x ∉ Set.Ioi t from hx), zero_mul, min_eq_right (le_of_not_gt hx)]
      linarith [min_le_right q x]
  have hb := integral_mono (hi.sub ht') (hk.mul_const (q-t)) hpoint
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hi ht', integral_mul_const] at hb
  have hkint : (∫ x, k x ∂D) = 1 - cdf D t := by
    simpa [k, integral_indicator measurableSet_Ioi, Measure.real] using tail D t
  rw [hkint] at hb
  exact hb

private theorem quantity_optimal (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s t : ℝ) (hsc : s < c) (hcμ : c < meanValuation ν)
    (heq : 1 - cdf D t = (c-s)/(reservationPrice ν s-s)) :
    0 ≤ t ∧ ∀ q, 0 ≤ q →
      (reservationPrice ν s-s)*SupplyChainTheory.expSales D q - (c-s)*q ≤
      (reservationPrice ν s-s)*SupplyChainTheory.expSales D t - (c-s)*t := by
  have hmean : meanValuation ν ≤ reservationPrice ν s := by
    exact integral_mono hν (hν.sup (integrable_const s)) (fun v => le_max_left v s)
  have hM : 0 < reservationPrice ν s-s := by linarith
  have hfrac : (c-s)/(reservationPrice ν s-s) < 1 := (div_lt_one hM).mpr (by linarith)
  have ht : 0 ≤ t := by
    by_contra h
    have hzero : D (Set.Iic t) = 0 := measure_mono_null
      (fun x hx => lt_of_le_of_lt hx (lt_of_not_ge h)) hD0
    have hcdf : cdf D t = 0 := by simp [cdf_eq_real, Measure.real, hzero]
    rw [hcdf] at heq
    linarith
  refine ⟨ht, ?_⟩
  intro q hq
  have hbound := mul_le_mul_of_nonneg_left (sales_support D hD0 q t hq ht) hM.le
  have hcancel : (reservationPrice ν s-s) * (1-cdf D t) = c-s := by
    rw [heq]
    exact mul_div_cancel₀ _ (ne_of_gt hM)
  nlinarith [hcancel]

private theorem optimal_margin (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s : ℝ) :
    margin ν s (reservationPrice ν s) s = reservationPrice ν s-s := by
  have hp := partition ν s
  unfold margin
  nlinarith [congrArg (fun z : ℝ => z * (reservationPrice ν s-s)) hp]

private theorem profit_form (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    (c s p q r : ℝ) :
    profit ν D c s p q r = margin ν s p r * sales ν D p q r - (c-s)*q := by
  have hp := partition ν r
  unfold profit margin
  nlinarith [congrArg (fun z : ℝ => z * (s*sales ν D p q r)) hp]

private theorem margin_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s p r : ℝ)
    (hp : p ≤ reservationPrice ν r) :
    margin ν s p r ≤ reservationPrice ν s-s := by
  have hk : 0 ≤ keepProb ν r := ENNReal.toReal_nonneg
  have hr : 0 ≤ returnProb ν r := ENNReal.toReal_nonneg
  have ha : margin ν s p r ≤ margin ν s (reservationPrice ν r) r := by
    unfold margin
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hk, mul_nonneg (sub_nonneg.mpr hp) hr]
  calc
    _ ≤ margin ν s (reservationPrice ν r) r := ha
    _ = ∫ v in Set.Ici r, (v-s) ∂ν := margin_identity ν hν s r
    _ ≤ ∫ v in Set.Ici s, (v-s) ∂ν := refund_bound ν hν s r
    _ = reservationPrice ν s-s := by
      rw [← margin_identity ν hν s s, optimal_margin ν hν s]

theorem SuReturns.PartialRefunds.proposition2_optimal_policy (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (qstar : ℝ) (hq : 1 - cdf D qstar = (c - s) / (reservationPrice ν s - s)) :
    ∀ p r q, 0 ≤ q → profit ν D c s p q r ≤ profit ν D c s (reservationPrice ν s) qstar s := by
  obtain ⟨ht, hopt⟩ := quantity_optimal ν D hν hD0 c s qstar hsc hcμ hq
  intro p r q hq0
  rw [profit_form, profit_form, optimal_margin ν hν s]
  simp only [sales, le_refl, ite_true]
  have hb := hopt q hq0
  by_cases hp : p ≤ reservationPrice ν r
  · rw [if_pos hp]
    exact le_trans (sub_le_sub_right
      (mul_le_mul_of_nonneg_right (margin_bound ν hν s p r hp)
        (sales_nonneg D hD0 q hq0)) _) hb
  · rw [if_neg hp, mul_zero, zero_sub]
    have hz := hopt 0 le_rfl
    have hs : SupplyChainTheory.expSales D 0 = 0 := by
      unfold SupplyChainTheory.expSales
      rw [integral_congr_ae (show (fun x => min (0 : ℝ) x) =ᵐ[D] fun _ => 0 from by
        filter_upwards [demand_nonneg D hD0] with x hx
        exact min_eq_left hx)]
      simp
    rw [hs] at hz
    nlinarith [mul_nonneg (sub_nonneg.mpr hsc.le) hq0]

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs0 : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν)
    (qstar : ℝ) (hq : 1 - cdf D qstar = (c - s) / (reservationPrice ν s - s)) :
    ∀ p r q, 0 ≤ q → profit ν D c s p q r ≤ profit ν D c s (reservationPrice ν s) qstar s :=
  SuReturns.PartialRefunds.proposition2_optimal_policy ν D hν hD0 c s hs0 hsc hcμ qstar hq

#print axioms solution
