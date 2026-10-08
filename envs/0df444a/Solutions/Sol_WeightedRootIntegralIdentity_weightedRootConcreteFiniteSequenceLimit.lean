-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootConcreteFiniteSequenceLimit
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T07:33:16.117905+00:00
-- url     : https://prove2.me/submissions/4bdd7708-74df-45e7-b1a6-bed936205668

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open Filter Topology
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ : ℝ) (U L ρ : ℂ)
    (hu : Tendsto (fun m : ℕ =>
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ))) atTop (𝓝 U))
    (hl : Tendsto (fun m : ℕ =>
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ))) atTop (𝓝 L))
    (hvr : Tendsto (fun m : ℕ =>
      weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ)) atTop (𝓝 0))
    (hvl : Tendsto (fun m : ℕ =>
      weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ)) atTop (𝓝 0))
    (hi : Tendsto (fun m : ℕ =>
      weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ))) atTop (𝓝 0))
    (ho : Tendsto (fun m : ℕ =>
      weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ)) atTop (𝓝 0))
    (hfinite : ∀ m : ℕ,
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ)) +
      weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ) = ρ) :
    U + L = ρ := by
  let S : ℕ → ℂ := fun m =>
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ)) +
      weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ)
  have hsum : Tendsto S atTop (𝓝 (U + L)) := by
    simpa [S] using (((((hu.add hl).add hvr).add hvl).add hi).add ho)
  have hconst : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := tendsto_const_nhds
  have hfun : S = fun _ : ℕ => ρ := by
    funext m
    simpa [S] using hfinite m
  rw [hfun] at hsum
  exact tendsto_nhds_unique hsum hconst
