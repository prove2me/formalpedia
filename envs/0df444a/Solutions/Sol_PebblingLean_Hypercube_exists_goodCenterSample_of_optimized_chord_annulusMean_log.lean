-- Prove2me | solution 1 for PebblingLean.Hypercube.exists_goodCenterSample_of_optimized_chord_annulusMean_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:22.969625+00:00
-- url     : https://prove2.me/submissions/1e806956-66b9-48f0-b07e-6771ed470d6b

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_optimized_chord_annulusMean_inv_two
public import Theorems.Thm_PebblingLean_FiniteProbability_exp_neg_le_inv_two_pow_succ_of_log_le


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_optimized_chord_annulusMean_inv_two
    hgap_pos hmu_pos hmean
    (exp_neg_le_inv_two_pow_succ_of_log_le n hlog)
end PebblingLean.Hypercube
