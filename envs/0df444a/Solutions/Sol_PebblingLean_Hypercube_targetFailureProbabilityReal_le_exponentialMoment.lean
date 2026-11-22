-- Prove2me | solution 1 for PebblingLean.Hypercube.targetFailureProbabilityReal_le_exponentialMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:52.532012+00:00
-- url     : https://prove2.me/submissions/134601f4-c0f0-4936-860a-44cd1e3af7ed

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_le_expect_div_of_event_le
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) {lam : ℝ} (hlam : 0 < lam) :
    targetFailureProbabilityReal (N := N) rIn rOut T target ≤
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam := by
  classical
  have hmarkov :=
    uniformProbabilityReal_le_expect_div_of_event_le
      (P := fun sample : CenterSample n N => sampleTargetFails rIn rOut T target sample)
      (X := fun sample : CenterSample n N =>
        Real.exp (lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ))))
      (a := 1)
      (by norm_num)
      (fun sample => Real.exp_nonneg _)
      (fun sample hfail => by
        have hlt :
            (sampleTotalContribution rIn rOut target sample : ℝ) < (T : ℝ) := by
          exact_mod_cast hfail
        have hdiff :
            0 < (T : ℝ) - (sampleTotalContribution rIn rOut target sample : ℝ) :=
          sub_pos.mpr hlt
        have harg :
            0 < lam * ((T : ℝ) -
              (sampleTotalContribution rIn rOut target sample : ℝ)) :=
          mul_pos hlam hdiff
        have hexp :
            Real.exp 0 <
              Real.exp (lam * ((T : ℝ) -
                (sampleTotalContribution rIn rOut target sample : ℝ))) :=
          Real.exp_lt_exp.mpr harg
        simpa using hexp.le)
  simpa [targetFailureProbabilityReal, targetLowerTailExponentialMoment] using hmarkov
end PebblingLean.Hypercube
