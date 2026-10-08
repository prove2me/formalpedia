-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootInstantiateActualFiniteComponents
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:14:26.79548+00:00
-- url     : https://prove2.me/submissions/1eebf7ef-293f-4114-beca-6de8cdafaf3e

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open Filter Topology
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ r R : ℝ) (U L ρ : ℂ)
    (hu : Tendsto (fun m : ℕ =>
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r) atTop (𝓝 U))
    (hl : Tendsto (fun m : ℕ =>
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r) atTop (𝓝 L))
    (hvr : Tendsto (fun m : ℕ =>
      weightedRootRightVerticalIntegral n a w a₁ r R) atTop (𝓝 0))
    (hvl : Tendsto (fun m : ℕ =>
      weightedRootLeftVerticalIntegral n a w a₀ r R) atTop (𝓝 0))
    (hi : Tendsto (fun m : ℕ =>
      weightedRootFiniteInnerArcIntegral n a w r) atTop (𝓝 0))
    (ho : Tendsto (fun m : ℕ =>
      weightedRootFiniteOuterArcIntegral n a w R) atTop (𝓝 0))
    (hfinite : ∀ m : ℕ,
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R = ρ) :
    U + L = ρ := by
  let S : ℂ :=
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R
  have hsum : Tendsto (fun _ : ℕ => S) atTop (𝓝 (U + L)) := by
    simpa [S] using (((((hu.add hl).add hvr).add hvl).add hi).add ho)
  have hconst : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := tendsto_const_nhds
  have hfun : (fun _ : ℕ => S) = (fun _ : ℕ => ρ) := by
    funext m
    simpa [S] using hfinite m
  rw [hfun] at hsum
  exact tendsto_nhds_unique hsum hconst
