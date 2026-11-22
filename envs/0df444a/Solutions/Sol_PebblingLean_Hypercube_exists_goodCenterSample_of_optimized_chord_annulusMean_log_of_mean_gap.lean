-- Prove2me | solution 1 for PebblingLean.Hypercube.exists_goodCenterSample_of_optimized_chord_annulusMean_log_of_mean_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:34.460661+00:00
-- url     : https://prove2.me/submissions/8e4cc631-bc39-4ce7-98f1-cc8e1437bcdc

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_optimized_chord_annulusMean_log

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
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by
  have hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  exact exists_goodCenterSample_of_optimized_chord_annulusMean_log
    hgap_pos hmu_pos hmean hlog
end PebblingLean.Hypercube
