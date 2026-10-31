-- Prove2me | solution 1 for RobustBooking.TwoFare.nested_protection_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:27:08.719091+00:00
-- url     : https://prove2.me/submissions/37fd0bc6-ebaf-4ae2-b567-b2c8f084778c

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies
import Theorems.Thm_RobustBooking_TwoFare_nested_protection_ratio
import Theorems.Thm_RobustBooking_TwoFare_randomized_upper_bound

open MeasureTheory

namespace RobustBooking.TwoFare

theorem nested_protection_optimal (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (nested n ((1 - b (f₂ / f₁)) * n)) = b (f₂ / f₁) ∧
    (∀ A : DetPolicy, competitiveRatio f₁ f₂ n A ≤ b (f₂ / f₁)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : Ω → DetPolicy), (∀ I : List Request, Measurable fun ω => revenue f₁ f₂ n (A ω) I) →
      randCompetitiveRatio f₁ f₂ n μ A ≤ b (f₂ / f₁)) := by
  refine ⟨nested_protection_ratio f₁ f₂ n hf₂ hf₁₂ hn, ?_, ?_⟩
  · intro A
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
  · intro Ω _ μ _ A hA
    exact (randomized_upper_bound f₁ f₂ n hf₂ hf₁₂ hn μ A hA).1

end RobustBooking.TwoFare

open RobustBooking.TwoFare MeasureTheory in
theorem solution (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (nested n ((1 - b (f₂ / f₁)) * n)) = b (f₂ / f₁) ∧
    (∀ A : DetPolicy, competitiveRatio f₁ f₂ n A ≤ b (f₂ / f₁)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : Ω → DetPolicy), (∀ I : List Request, Measurable fun ω => revenue f₁ f₂ n (A ω) I) →
      randCompetitiveRatio f₁ f₂ n μ A ≤ b (f₂ / f₁)) :=
  nested_protection_optimal f₁ f₂ n hf₂ hf₁₂ hn
