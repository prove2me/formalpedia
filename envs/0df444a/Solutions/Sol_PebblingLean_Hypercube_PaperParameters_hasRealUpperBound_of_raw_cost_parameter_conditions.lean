-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_raw_cost_parameter_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:17:55.264799+00:00
-- url     : https://prove2.me/submissions/6a65a24b-b905-4873-b18b-3d4213989c92

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_add_splitM_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_normalizedCost_step_of_cost_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_parameter_conditions

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {costBound sampleCount : ℕ → ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost costBound n ≤ B)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < demandGap K costBound n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM K n) : ℝ) + demandGap K costBound n ≤
          (sampleCount n : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (demandGap K costBound n) ^ 2 /
            (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
              ((sampleCount n : ℝ) *
                (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        sampleCount n * 2 ^ rOut A K n ≤
          minPile (splitM K n) * costMultiplier K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM K n) * costMultiplier K n ≤ costBound n)
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hcostReal :
      ∀ n : ℕ, n0 ≤ n →
        (costBound n : ℝ) ≤
          (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
            (costBound (splitM K n) : ℝ)) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * loss n0) * B) :=
  hasRealUpperBound_of_parameter_conditions
    (K := K) (A := A) (n0 := n0) (costBound := costBound)
    (sampleCount := sampleCount) (B := B)
    hn0_pos hB hbase_cost hbase_norm hquarter hgap_pos hmean hlog
    hfiberCost hcost hminExp
    (fun n hn =>
      normalizedCost_step_of_cost_le
        (splitA_add_splitM_of_four_mul_le (hquarter n hn))
        (hcostReal n hn))
end PebblingLean.Hypercube.PaperParameters
