-- Prove2me | solution 1 for PebblingLean.Hypercube.exists_goodCenterSample_of_optimized_chord_annulusMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:24.146499+00:00
-- url     : https://prove2.me/submissions/c2c161bc-2301-491a-adce-2c115367b487

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_bernsteinTargetFailureBound_of_optimized_chord_annulusMean
public import Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_bernstein_bound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_bernstein_bound
    (bernsteinTargetFailureBound_of_optimized_chord_annulusMean
      hgap_pos hmu_pos hmean hexp)
    hunion
end PebblingLean.Hypercube
