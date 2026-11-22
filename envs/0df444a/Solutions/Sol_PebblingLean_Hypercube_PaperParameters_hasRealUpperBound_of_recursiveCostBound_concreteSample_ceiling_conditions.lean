-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:16:59.854736+00:00
-- url     : https://prove2.me/submissions/57af2ac2-86ff-45b3-9829-0f23583772f0

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_base_cost
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_one_le_minPile
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_demandGapForDemand_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_of_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_decay_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_add_splitM_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_lt_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_step_cost
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_minPile_le_stackSize_of_exponent_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_fiberCost
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_normalizedCost_recursiveCostBound_step_of_ceiling
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_hasHypercubePebblingUpperBound_of_recursive_split_schedule_variable_large_constant_base
public import Theorems.Thm_PebblingLean_Hypercube_hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right
attribute [local simp] PebblingLean.Pebbling.weight_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost (recursiveCostBound K n0) n ≤ B)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (t : ℝ) + demandGapForDemand n t ≤
            (sampleCountForDemand A K n t : ℝ) *
              (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (demandGapForDemand n t) ^ 2 /
              (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
                ((sampleCountForDemand A K n t : ℝ) *
                  (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hstack :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (2 ^ rOut A K n : ℝ) ≤
            (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n))
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound (Real.exp (4 * loss n0) * B) := by
  have hupper : HasHypercubePebblingUpperBound (recursiveCostBound K n0) :=
    hasHypercubePebblingUpperBound_of_recursive_split_schedule_variable_large_constant_base
      (costBound := recursiveCostBound K n0) (minPile := minPile)
      (splitA := splitA K) (splitM := splitM K)
      (K := costMultiplier K) (N := sampleCountForDemand A K)
      (rIn := rIn A K) (rOut := rOut A K)
      (gap := fun n t => demandGapForDemand n t) (n0 := n0)
      (fun n hn => one_le_minPile n)
      recursiveCostBound_base_cost
      (fun n hn => splitA_add_splitM_of_four_mul_le (hquarter n hn))
      (fun n hn => splitM_lt_of_four_mul_le hn0_pos hn (hquarter n hn))
      (fun n hn t ht => by
        have hn_pos : 0 < n := lt_of_lt_of_le hn0_pos hn
        have ht_pos : 0 < t :=
          lt_of_lt_of_le Nat.zero_lt_one ((one_le_minPile (splitM K n)).trans ht)
        exact demandGapForDemand_pos hn_pos ht_pos)
      hmean
      hlog
      (fun n hn t ht => sampleCountForDemand_fiberCost (hstack n hn t ht))
      (recursiveCostBound_step_cost hn0_pos hquarter)
      (fun n hn => minPile_le_stackSize_of_exponent_le (hminExp n hn))
  have hfinal :
      HasRealHypercubePebblingUpperBound (Real.exp (2 * (2 * loss n0)) * B) :=
    hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
      (costBound := recursiveCostBound K n0) (next := splitM K)
      (loss := fun n => 2 * loss n)
      (n0 := n0) (B := B) (q := (1 : ℝ) / 2) (M := 2 * loss n0)
      hupper
      (fun n => mul_nonneg (by norm_num) (loss_nonneg n))
      hB
      (mul_nonneg (by norm_num) (loss_nonneg n0))
      (by norm_num)
      (by norm_num)
      (fun n hn => splitM_lt_of_four_mul_le hn0_pos hn (hquarter n hn))
      (fun n hn =>
        normalizedCost_recursiveCostBound_step_of_ceiling
          hn (splitM_lt_of_four_mul_le hn0_pos hn (hquarter n hn))
          (hceilSlack n hn))
      hbase_norm
      (fun n hn hnext => by
        have hdecay :=
          loss_decay_of_four_mul_le
            (lt_of_lt_of_le hn0_pos hnext) (hquarter n hn)
        nlinarith)
      (fun n hn => by
        have hle := loss_le_of_le hn0_pos hn
        nlinarith)
  simpa [show 2 * (2 * loss n0) = 4 * loss n0 by ring] using hfinal
end PebblingLean.Hypercube.PaperParameters
