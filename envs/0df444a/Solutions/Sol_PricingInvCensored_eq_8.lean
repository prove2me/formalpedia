-- Prove2me | solution 1 for PricingInvCensored.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:36:25.701953+00:00
-- url     : https://prove2.me/submissions/405d88f4-0057-461f-a0d9-3babde6447e7

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open MeasureTheory Set

open PricingInvCensored in
theorem solution (I : Instance) (pStar yStar : ℝ) (hA : Assumption1 I pStar yStar) (p p' : ℝ)
    (hp : p ∈ Icc I.market.low I.market.high) (hp' : p' ∈ Icc I.market.low I.market.high)
    (hpp' : p < p') (z z' : ℝ) (hz : I.market.cdf z = I.market.quantileLevel p)
    (hz' : I.market.cdf z' = I.market.quantileLevel p') :
    z < z' ∧
      1 - I.market.quantileLevel p = I.market.h / (I.market.b + p + I.market.h) ∧
      I.market.h / (I.market.b + p + I.market.h) = (I.market.noise (Ici z)).toReal ∧
      (I.market.noise (Ici z)).toReal =
        (I.market.noise {ε : ℝ | max (z' - ε) 0 ≤ z' - z}).toReal := by
  haveI := hA.noise_prob
  have hb := hA.b_nonneg
  have hh := hA.h_pos
  have hl := hA.low_nonneg
  have hd1 : 0 < I.market.b + p + I.market.h := by linarith [hp.1]
  have hd2 : 0 < I.market.b + p' + I.market.h := by linarith [hp'.1]
  have hq : I.market.quantileLevel p < I.market.quantileLevel p' := by
    unfold ChenChaoShiSALA.Regret.Market.quantileLevel
    rw [div_lt_div_iff₀ hd1 hd2]
    nlinarith [mul_lt_mul_of_pos_right hpp' hh]
  have hzz : z < z' := by
    by_contra hc
    push_neg at hc
    have hmono : I.market.cdf z' ≤ I.market.cdf z := by
      unfold ChenChaoShiSALA.Regret.Market.cdf
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hc))
    linarith
  have h1q : 1 - I.market.quantileLevel p = I.market.h / (I.market.b + p + I.market.h) := by
    unfold ChenChaoShiSALA.Regret.Market.quantileLevel
    rw [eq_div_iff hd1.ne', sub_mul, div_mul_cancel₀ _ hd1.ne']
    ring
  have hatom : I.market.noise {z} = 0 := by
    rw [hA.noise_density]
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  have hIoi : I.market.noise (Ioi z) = I.market.noise (Ici z) := measure_congr (Ioi_ae_eq_Ici' hatom)
  have hsum := measure_add_measure_compl (μ := I.market.noise) (measurableSet_Iic (a := z))
  rw [compl_Iic, measure_univ] at hsum
  have hsumR : (I.market.noise (Iic z)).toReal + (I.market.noise (Ioi z)).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum, ENNReal.toReal_one]
  have hcdf : I.market.cdf z = (I.market.noise (Iic z)).toReal := rfl
  refine ⟨hzz, h1q, ?_, ?_⟩
  · rw [← h1q, ← hz, hcdf, ← hIoi]
    linarith
  · congr 2
    ext ε
    simp only [mem_setOf_eq, mem_Ici, max_le_iff]
    constructor
    · intro h; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h, -⟩; linarith
