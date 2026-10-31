-- Prove2me | solution 1 for RobustBooking.TwoFare.deterministic_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:08:37.799036+00:00
-- url     : https://prove2.me/submissions/8e4d65bd-29c1-42fc-8ed8-3e2f9cb33161

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies
import Theorems.Thm_RobustBooking_TwoFare_randomized_upper_bound

open MeasureTheory RobustBooking.TwoFare

theorem solution (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    (A : DetPolicy) :
    competitiveRatio f₁ f₂ n A ≤ b (f₂ / f₁) := by
  let μ : Measure Unit := Measure.dirac ()
  have hprob : IsProbabilityMeasure μ := Measure.dirac.isProbabilityMeasure
  have h1 := (randomized_upper_bound f₁ f₂ n hf₂ hf₁₂ hn μ (fun _ => A)
    (fun _ => measurable_const)).1
  have heq : competitiveRatio f₁ f₂ n A = randCompetitiveRatio f₁ f₂ n μ (fun _ => A) := by
    unfold competitiveRatio randCompetitiveRatio
    congr 1
    ext c
    simp [μ]
  rw [heq]
  exact h1
