-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:10.87159+00:00
-- url     : https://prove2.me/submissions/cd5bb996-5613-4e18-b8a6-46df3eaff776

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
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
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) :=
  hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
    hgap_pos hmu_pos hmean
    (exp_neg_le_inv_two_pow_succ_of_log_le n hlog)
end PebblingLean.Hypercube
