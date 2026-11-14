-- Prove2me | solution 1 for StabilityDichotomies.Approximability.weighted_influence_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:22:35.437293+00:00
-- url     : https://prove2.me/submissions/eed73b43-aaa4-46ea-a762-2fd139be4013

import Mathlib
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory

theorem solution
    (ε B : ℝ) (hε : 0 ≤ ε) (F d : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.uIcc (1 - ε) 1, HasDerivAt F (d t) t)
    (hint : IntervalIntegrable d volume (1 - ε) 1)
    (hnonneg : ∀ t ∈ Set.Icc (1 - ε) 1, 0 ≤ d t)
    (hbound : F 1 - F (1 - ε) ≤ B) :
    (∫ t in (1 - ε)..1, t * d t) ≤ B := by
  have hab : 1 - ε ≤ 1 := by linarith
  have hw : IntervalIntegrable (fun t => t * d t) volume (1 - ε) 1 := by
    convert hint.mul_continuousOn continuous_id.continuousOn using 1 <;> funext t <;> simp only [id_eq] <;> ring
  calc
    _ ≤ ∫ t in (1 - ε)..1, d t := by
      apply intervalIntegral.integral_mono_on hab hw hint
      intro t ht
      have ht1 := ht.2
      have hd := hnonneg t ht
      nlinarith
    _ = F 1 - F (1 - ε) := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ ≤ B := hbound
