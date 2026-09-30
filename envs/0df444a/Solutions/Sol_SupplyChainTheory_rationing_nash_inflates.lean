-- Prove2me | solution 1 for SupplyChainTheory.rationing_nash_inflates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:08:24.008436+00:00
-- url     : https://prove2.me/submissions/389af534-2372-4b75-90a5-014a21160750

import Mathlib
import Definitions.Def_SupplyChainTheory_bullwhip

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

section Rationing

lemma rat_null (D : Measure ℝ) [IsProbabilityMeasure D] (hc : Continuous (cdf D)) :
    NullSingletonClass D := by
  refine ⟨fun a => ?_⟩
  have h1 := (cdf D).measure_singleton a
  rw [measure_cdf] at h1
  rw [h1]
  have hl : Function.leftLim (cdf D) a = cdf D a :=
    (monotone_cdf D).continuousWithinAt_Iio_iff_leftLim_eq.mp hc.continuousAt.continuousWithinAt
  rw [hl, sub_self, ENNReal.ofReal_zero]

lemma rat_int_min (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : Integrable (fun d => min Q d) D := by
  refine Integrable.mono' ((integrable_const |Q|).add hD.abs)
    (measurable_const.min measurable_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rcases le_total Q d with h | h
  · rw [min_eq_left h]; linarith [abs_nonneg d]
  · rw [min_eq_right h]; linarith [abs_nonneg Q]

lemma rat_sales_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (Q0 : ℝ) :
    HasDerivAt (fun Q => ∫ d, min Q d ∂D) (1 - cdf D Q0) Q0 := by
  have hlip : ∀ d : ℝ, LipschitzOnWith (Real.nnabs 1) (fun Q : ℝ => min Q d) Set.univ := by
    intro d
    have : Real.nnabs 1 = 1 := by simp
    rw [this]
    exact (LipschitzWith.id.min_const d).lipschitzOnWith
  have hdiff : ∀ d : ℝ, d ≠ Q0 →
      HasDerivAt (fun Q : ℝ => min Q d) (if Q0 < d then (1:ℝ) else 0) Q0 := by
    intro d hd
    rcases lt_or_gt_of_ne hd with h | h
    · rw [if_neg (not_lt.mpr h.le)]
      apply (hasDerivAt_const Q0 d).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h] with Q hQ
      exact min_eq_right (le_of_lt hQ)
    · rw [if_pos h]
      apply (hasDerivAt_id Q0).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds h] with Q hQ
      exact min_eq_left (le_of_lt hQ)
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := D)
    (F := fun Q d => min Q d) (F' := fun d => if Q0 < d then (1:ℝ) else 0)
    (bound := fun _ => (1:ℝ)) (s := Set.univ) (x₀ := Q0) Filter.univ_mem
    (Filter.Eventually.of_forall fun Q =>
      (measurable_const.min measurable_id).aestronglyMeasurable)
    (rat_int_min D hD Q0)
    ((Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun d => hlip d)
    (integrable_const 1)
    ((Measure.ae_ne D Q0).mono fun d hd => hdiff d hd)
  have hval : ∫ d, (if Q0 < d then (1:ℝ) else 0) ∂D = 1 - cdf D Q0 := by
    have e : (fun d : ℝ => if Q0 < d then (1:ℝ) else 0) = (Set.Ioi Q0).indicator 1 := by
      funext d; simp [Set.indicator_apply]
    rw [e, integral_indicator_one measurableSet_Ioi, cdf_eq_real, ← Set.compl_Iic,
      measureReal_compl measurableSet_Iic, probReal_univ]
  rw [← hval]
  exact key.2

lemma rat_int_id (D : Measure ℝ) [IsProbabilityMeasure D] {h p : ℝ} (hh : 0 < h) (hp : 0 < p)
    (hint : Integrable (fun d => h * max (0 - d) 0 + p * max (d - 0) 0) D) :
    Integrable (fun x => x) D := by
  set m := min h p with hmdef
  have hm : 0 < m := lt_min hh hp
  have hmh : m ≤ h := min_le_left h p
  have hmp : m ≤ p := min_le_right h p
  refine Integrable.mono' (hint.const_mul (1 / m)) measurable_id.aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs]
  have h1 : m * |d| ≤ h * max (0 - d) 0 + p * max (d - 0) 0 := by
    rcases le_total 0 d with hd | hd
    · rw [abs_of_nonneg hd, max_eq_right (by linarith), max_eq_left (by linarith)]
      nlinarith
    · rw [abs_of_nonpos hd, max_eq_left (by linarith), max_eq_right (by linarith)]
      nlinarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
  linarith

lemma rat_G_eq (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (h p y : ℝ) :
    ∫ d, (h * max (y - d) 0 + p * max (d - y) 0) ∂D =
      h * (y - ∫ d, min y d ∂D) + p * ((∫ d, d ∂D) - ∫ d, min y d ∂D) := by
  have hpt : ∀ d, h * max (y - d) 0 + p * max (d - y) 0 = h * (y - min y d) + p * (d - min y d) := by
    intro d
    rcases le_total y d with hyd | hyd
    · rw [min_eq_left hyd, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [min_eq_right hyd, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  simp_rw [hpt]
  have i1 := rat_int_min D hD y
  have i2 : Integrable (fun d => h * (y - min y d)) D := ((integrable_const y).sub i1).const_mul h
  have i3 : Integrable (fun d => p * (d - min y d)) D := (hD.sub i1).const_mul p
  rw [integral_add i2 i3, integral_const_mul, integral_const_mul,
    integral_sub (integrable_const y) i1, integral_sub hD i1, integral_const]
  simp

lemma rat_G_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (h p y : ℝ) :
    HasDerivAt (fun y => ∫ d, (h * max (y - d) 0 + p * max (d - y) 0) ∂D)
      ((h + p) * cdf D y - p) y := by
  have hS := rat_sales_deriv D hD y
  have e : (fun y => ∫ d, (h * max (y - d) 0 + p * max (d - y) 0) ∂D) =
      fun y => h * (y - ∫ d, min y d ∂D) + p * ((∫ d, d ∂D) - ∫ d, min y d ∂D) :=
    funext (rat_G_eq D hD h p)
  rw [e]
  have := (((hasDerivAt_id' y).sub hS).const_mul h).add
    (((hasDerivAt_const y (∫ d, d ∂D)).sub hS).const_mul p)
  have e2 : h * (1 - (1 - cdf D y)) + p * (0 - (1 - cdf D y)) = (h + p) * cdf D y - p := by ring
  rw [e2] at this
  exact this

theorem rat_main (h p r A1 Qstar Q : ℝ) (Dlaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dlaw]
    (hh : 0 < h) (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hA : 0 < A1)
    (hint : ∀ y : ℝ, MeasureTheory.Integrable
      (fun d => h * max (y - d) 0 + p * max (d - y) 0) Dlaw)
    (hFc : Continuous (ProbabilityTheory.cdf Dlaw))
    (hFmono : StrictMonoOn (ProbabilityTheory.cdf Dlaw) (Set.Ici 0))
    (hQs0 : 0 ≤ Qstar) (hQstar : ProbabilityTheory.cdf Dlaw Qstar = p / (h + p))
    (hA2 : A1 < 2 * Qstar) (hQpos : 0 < Q)
    (hNash : ∀ Q1 : ℝ, 0 < Q1 →
      rationingCost h p r A1 Dlaw Q Q ≤ rationingCost h p r A1 Dlaw Q Q1) :
    Qstar < Q := by
  haveI := rat_null Dlaw hFc
  have hD := rat_int_id Dlaw hh hp (hint 0)
  by_contra hle
  push Not at hle
  set G : ℝ → ℝ := fun y => ∫ d, (h * max (y - d) 0 + p * max (d - y) 0) ∂Dlaw with hG
  have hGd : ∀ y, HasDerivAt G ((h + p) * cdf Dlaw y - p) y := fun y => rat_G_deriv Dlaw hD h p y
  have hQQ : Q + Q ≠ 0 := by linarith
  have ha : HasDerivAt (fun Q1 => A1 * Q1 / (Q1 + Q))
      ((A1 * 1 * (Q + Q) - A1 * Q * 1) / (Q + Q) ^ 2) Q :=
    ((hasDerivAt_id' Q).const_mul A1).div ((hasDerivAt_id' Q).add_const Q) hQQ
  have haQ : A1 * Q / (Q + Q) = A1 / 2 := by field_simp; ring
  set φ : ℝ → ℝ := fun Q1 => (1 - r) * G Q1 + r * G (A1 * Q1 / (Q1 + Q)) with hφdef
  have hcomp : HasDerivAt (fun Q1 => G (A1 * Q1 / (Q1 + Q)))
      (((h + p) * cdf Dlaw (A1 * Q / (Q + Q)) - p) *
        ((A1 * 1 * (Q + Q) - A1 * Q * 1) / (Q + Q) ^ 2)) Q :=
    HasDerivAt.comp (x := Q) (h₂ := G) (h := fun Q1 => A1 * Q1 / (Q1 + Q))
      (hGd (A1 * Q / (Q + Q))) ha
  have hφ : HasDerivAt φ ((1 - r) * ((h + p) * cdf Dlaw Q - p) +
      r * (((h + p) * cdf Dlaw (A1 * Q / (Q + Q)) - p) *
        ((A1 * 1 * (Q + Q) - A1 * Q * 1) / (Q + Q) ^ 2))) Q :=
    ((hGd Q).const_mul (1 - r)).add (hcomp.const_mul r)
  have hF1 : cdf Dlaw Q ≤ p / (h + p) := hQstar ▸ monotone_cdf Dlaw hle
  have hF2 : cdf Dlaw (A1 / 2) < p / (h + p) := by
    rw [← hQstar]
    exact hFmono (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hQs0) (by linarith)
  have hhp : 0 < h + p := by linarith
  have hneg : (1 - r) * ((h + p) * cdf Dlaw Q - p) +
      r * (((h + p) * cdf Dlaw (A1 * Q / (Q + Q)) - p) *
        ((A1 * 1 * (Q + Q) - A1 * Q * 1) / (Q + Q) ^ 2)) < 0 := by
    rw [haQ]
    have e1 : (h + p) * cdf Dlaw Q - p ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hF1 hhp.le
      rw [mul_div_cancel₀ _ hhp.ne'] at this
      linarith
    have e2 : (h + p) * cdf Dlaw (A1 / 2) - p < 0 := by
      have := mul_lt_mul_of_pos_left hF2 hhp
      rw [mul_div_cancel₀ _ hhp.ne'] at this
      linarith
    have e3 : 0 < (A1 * 1 * (Q + Q) - A1 * Q * 1) / (Q + Q) ^ 2 := by
      apply div_pos _ (by positivity)
      nlinarith
    have e4 : (1 - r) * ((h + p) * cdf Dlaw Q - p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) e1
    have e5 : r * (((h + p) * cdf Dlaw (A1 / 2) - p) *
        ((A1 * 1 * (Q + Q) - A1 * Q * 1) / (Q + Q) ^ 2)) < 0 :=
      mul_neg_of_pos_of_neg hr0 (mul_neg_of_neg_of_pos e2 e3)
    linarith
  have hslope := hφ.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t⁻¹ • (φ (Q + t) - φ Q) < 0 :=
    hslope (Iio_mem_nhds hneg)
  have hpos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht1, ht2⟩ := (hev.and hpos).exists
  rw [smul_eq_mul] at ht1
  have hlt : φ (Q + t) < φ Q := by
    by_contra hc
    push Not at hc
    have := mul_nonneg (inv_pos.mpr ht2).le (sub_nonneg.mpr hc)
    linarith
  have hN := hNash (Q + t) (by linarith)
  have eQ : rationingCost h p r A1 Dlaw Q Q = φ Q := rfl
  have eQt : rationingCost h p r A1 Dlaw Q (Q + t) = φ (Q + t) := rfl
  rw [eQ, eQt] at hN
  linarith

end Rationing

end SupplyChainTheory

open SupplyChainTheory

theorem solution (h p r A1 Qstar Q : ℝ) (Dlaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dlaw]
    (hh : 0 < h) (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hA : 0 < A1)
    (hint : ∀ y : ℝ, MeasureTheory.Integrable (fun d => h * max (y - d) 0 + p * max (d - y) 0) Dlaw)
    (hFc : Continuous (ProbabilityTheory.cdf Dlaw))
    (hFmono : StrictMonoOn (ProbabilityTheory.cdf Dlaw) (Set.Ici 0))
    (hQs0 : 0 ≤ Qstar) (hQstar : ProbabilityTheory.cdf Dlaw Qstar = p / (h + p))
    (hA2 : A1 < 2 * Qstar) (hQpos : 0 < Q)
    (hNash : ∀ Q1 : ℝ, 0 < Q1 →
      rationingCost h p r A1 Dlaw Q Q ≤ rationingCost h p r A1 Dlaw Q Q1) :
    Qstar < Q := by
  exact rat_main h p r A1 Qstar Q Dlaw hh hp hr0 hr1 hA hint hFc hFmono hQs0 hQstar hA2 hQpos hNash
