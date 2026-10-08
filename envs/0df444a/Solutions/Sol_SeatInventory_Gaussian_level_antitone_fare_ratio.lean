-- Prove2me | solution 1 for SeatInventory.Gaussian.level_antitone_fare_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:17:21.91845+00:00
-- url     : https://prove2.me/submissions/653f5e07-7bbd-4f39-9012-c98c740c0290

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem SeatInventory_Gaussian_tail_anti_17021870 (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a ≤ b) : tailProb μ b ≤ tailProb μ a := by
  unfold tailProb
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ici_subset_Ici.mpr hab))

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem solution (rbar σ f₁ f₂ g₁ g₂ Z Z' S S' : ℝ) (hσ : 0 < σ)
    (hf₂ : 0 < f₂) (hf : f₂ < f₁) (hg₂ : 0 < g₂) (hg : g₂ < g₁) (hlt : f₂ / f₁ < g₂ / g₁)
    (hZ : IsStdNormalLevel f₁ f₂ Z) (hZ' : IsStdNormalLevel g₁ g₂ Z')
    (hS : IsProtectionLevel rbar σ f₁ f₂ S) (hS' : IsProtectionLevel rbar σ g₁ g₂ S') :
    Z' < Z ∧ S' < S := by
  have : IsProbabilityMeasure stdNormal :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have : IsProbabilityMeasure (gaussianLaw rbar σ) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold IsStdNormalLevel at hZ hZ'
  unfold IsProtectionLevel at hS hS'
  constructor
  · by_contra h
    replace h := not_lt.mp h
    have := SeatInventory_Gaussian_tail_anti_17021870 stdNormal Z Z' h
    rw [hZ, hZ'] at this
    linarith
  · by_contra h
    replace h := not_lt.mp h
    have := SeatInventory_Gaussian_tail_anti_17021870 (gaussianLaw rbar σ) S S' h
    rw [hS, hS'] at this
    linarith
