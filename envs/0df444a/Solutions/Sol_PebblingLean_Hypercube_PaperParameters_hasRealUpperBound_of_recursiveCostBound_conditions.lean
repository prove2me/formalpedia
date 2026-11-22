-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:18:40.786626+00:00
-- url     : https://prove2.me/submissions/ec71a3ce-dd17-43ff-b643-5b2293a6763d

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_base_cost
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_step_cost
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_raw_cost_parameter_conditions

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {sampleCount : ℕ → ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost (recursiveCostBound K n0) n ≤ B)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        0 < demandGap K (recursiveCostBound K n0) n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (recursiveCostBound K n0 (splitM K n) : ℝ) +
            demandGap K (recursiveCostBound K n0) n ≤
          (sampleCount n : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (demandGap K (recursiveCostBound K n0) n) ^ 2 /
            (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
              ((sampleCount n : ℝ) *
                (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        sampleCount n * 2 ^ rOut A K n ≤
          minPile (splitM K n) * costMultiplier K n)
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hcostReal :
      ∀ n : ℕ, n0 ≤ n →
        (recursiveCostBound K n0 n : ℝ) ≤
          (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
            (recursiveCostBound K n0 (splitM K n) : ℝ)) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * loss n0) * B) :=
  hasRealUpperBound_of_raw_cost_parameter_conditions
    (K := K) (A := A) (n0 := n0)
    (costBound := recursiveCostBound K n0)
    (sampleCount := sampleCount) (B := B)
    hn0_pos hB
    recursiveCostBound_base_cost
    hbase_norm
    hquarter
    hgap_pos
    hmean
    hlog
    hfiberCost
    (recursiveCostBound_step_cost hn0_pos hquarter)
    hminExp
    hcostReal
end PebblingLean.Hypercube.PaperParameters
