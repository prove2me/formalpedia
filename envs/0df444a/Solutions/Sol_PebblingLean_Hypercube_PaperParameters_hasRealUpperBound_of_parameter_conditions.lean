-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_parameter_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:16:58.884145+00:00
-- url     : https://prove2.me/submissions/25af07f4-80de-4898-a39a-15600a11c8a3

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_one_le_minPile
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_of_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_decay_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_add_splitM_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_lt_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_minPile_le_stackSize_of_exponent_le
public import Theorems.Thm_PebblingLean_Hypercube_hasHypercubePebblingUpperBound_of_recursive_split_schedule_large_constant_base
public import Theorems.Thm_PebblingLean_Hypercube_hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss


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
    (hnormStep :
      ∀ n : ℕ, n0 ≤ n →
        normalizedCost costBound n ≤
          (1 + loss n) * normalizedCost costBound (splitM K n)) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * loss n0) * B) := by
  have hupper : HasHypercubePebblingUpperBound costBound :=
    hasHypercubePebblingUpperBound_of_recursive_split_schedule_large_constant_base
      (costBound := costBound) (minPile := minPile)
      (splitA := splitA K) (splitM := splitM K)
      (K := costMultiplier K) (N := sampleCount)
      (rIn := rIn A K) (rOut := rOut A K)
      (gap := demandGap K costBound) (n0 := n0)
      (fun n hn => one_le_minPile n)
      hbase_cost
      (fun n hn => splitA_add_splitM_of_four_mul_le (hquarter n hn))
      (fun n hn => splitM_lt_of_four_mul_le hn0_pos hn (hquarter n hn))
      hgap_pos hmean hlog hfiberCost hcost
      (fun n hn => minPile_le_stackSize_of_exponent_le (hminExp n hn))
  exact hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
    (costBound := costBound) (next := splitM K) (loss := loss)
    (n0 := n0) (B := B) (q := (1 : ℝ) / 2) (M := loss n0)
    hupper
    loss_nonneg
    hB
    (loss_nonneg n0)
    (by norm_num)
    (by norm_num)
    (fun n hn => splitM_lt_of_four_mul_le hn0_pos hn (hquarter n hn))
    hnormStep
    hbase_norm
    (fun n hn hnext =>
      loss_decay_of_four_mul_le
        (lt_of_lt_of_le hn0_pos hnext) (hquarter n hn))
    (fun n hn => loss_le_of_le hn0_pos hn)
end PebblingLean.Hypercube.PaperParameters
