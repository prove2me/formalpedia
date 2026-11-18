-- Prove2me | solution 1 for PricingInvCensored.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:26:32.995959+00:00
-- url     : https://prove2.me/submissions/2a7c9f17-b9a4-4ea1-8c76-094801677e37

import Mathlib

open MeasureTheory Set
namespace PricingInvCensored

theorem eq_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (z z' : ℝ) (hzz : z ≤ z') :
    (∫ ε, max (ε - z) 0 ∂μ) - (∫ ε, max (ε - z') 0 ∂μ) =
        ∫ ε, (max (ε - z) 0 - max (ε - z') 0) ∂μ ∧
      ∫ ε, (max (ε - z) 0 - max (ε - z') 0) ∂μ =
        (z' - z) * (μ (Ici z)).toReal - ∫ ε in Icc z z', (z' - ε) ∂μ := by
  have i1 : Integrable (fun ε : ℝ => max (ε - z) 0) μ := (hμ.sub (integrable_const z)).pos_part
  have i2 : Integrable (fun ε : ℝ => max (ε - z') 0) μ := (hμ.sub (integrable_const z')).pos_part
  refine ⟨(integral_sub i1 i2).symm, ?_⟩
  have hpt : (fun ε : ℝ => max (ε - z) 0 - max (ε - z') 0) =
      fun ε => (Ici z).indicator (fun _ => z' - z) ε - (Icc z z').indicator (fun e => z' - e) ε := by
    funext ε
    by_cases h1 : z ≤ ε
    · by_cases h2 : ε ≤ z'
      · rw [indicator_of_mem (show ε ∈ Ici z from h1), indicator_of_mem (show ε ∈ Icc z z' from ⟨h1, h2⟩)]
        rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [indicator_of_mem (show ε ∈ Ici z from h1),
          indicator_of_notMem (show ε ∉ Icc z z' from fun h => h2 h.2)]
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    · rw [indicator_of_notMem (show ε ∉ Ici z from h1),
        indicator_of_notMem (show ε ∉ Icc z z' from fun h => h1 h.1)]
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]; try ring
  have hI : Integrable (fun e => (Icc z z').indicator (fun e => z' - e) e) μ := by
    exact ((integrable_const z').sub hμ).indicator measurableSet_Icc
  rw [hpt, integral_sub ((integrable_const _).indicator measurableSet_Ici)
      hI,
    integral_indicator_const _ measurableSet_Ici, integral_indicator measurableSet_Icc,
    measureReal_def, smul_eq_mul, mul_comm]

end PricingInvCensored

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (z z' : ℝ) (hzz : z ≤ z') :
    (∫ ε, max (ε - z) 0 ∂μ) - (∫ ε, max (ε - z') 0 ∂μ) =
        ∫ ε, (max (ε - z) 0 - max (ε - z') 0) ∂μ ∧
      ∫ ε, (max (ε - z) 0 - max (ε - z') 0) ∂μ =
        (z' - z) * (μ (Ici z)).toReal - ∫ ε in Icc z z', (z' - ε) ∂μ :=
  PricingInvCensored.eq_7 μ hμ z z' hzz
