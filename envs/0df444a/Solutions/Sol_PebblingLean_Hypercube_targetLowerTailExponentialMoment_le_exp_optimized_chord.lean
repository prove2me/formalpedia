-- Prove2me | solution 1 for PebblingLean.Hypercube.targetLowerTailExponentialMoment_le_exp_optimized_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:09.205151+00:00
-- url     : https://prove2.me/submissions/48dc0a34-0ef2-4a5e-93e9-6f4d10b53c48

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_le_exp_chord
public import Theorems.Thm_PebblingLean_FiniteProbability_exp_chord_quadratic_optimized
public import Theorems.Thm_PebblingLean_FiniteProbability_one_sub_exp_neg_ge_sub_sq
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
theorem _root_.solution
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {gap : ℝ}
    (hgap : 0 ≤ gap)
    (hmu_pos :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hmean :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target
        (gap /
          (2 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target))) ≤
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by
  classical
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let m : ℝ := oneCenterContributionExpectationReal rIn rOut target
  let mu : ℝ := (N : ℝ) * m
  let lam : ℝ := gap / (2 * B * mu)
  have hB_pos : 0 < B := by positivity
  have hB_nonneg : 0 ≤ B := hB_pos.le
  have hmu_pos' : 0 < mu := by simpa [mu, m]
  have hmu_nonneg : 0 ≤ mu := hmu_pos'.le
  have hlam_nonneg : 0 ≤ lam := by
    exact div_nonneg hgap (by positivity)
  have hm_nonneg : 0 ≤ m := by
    unfold m oneCenterContributionExpectationReal uniformExpectationReal
    exact div_nonneg
      (Finset.sum_nonneg fun center _hcenter => by positivity)
      (by positivity)
  have hq_lower :
      lam * B - (lam * B) ^ 2 ≤
        1 - Real.exp (-(lam * B)) := by
    exact one_sub_exp_neg_ge_sub_sq (mul_nonneg hlam_nonneg hB_nonneg)
  have hcoeff_nonneg : 0 ≤ (N : ℝ) * (m / B) := by
    exact mul_nonneg (by positivity) (div_nonneg hm_nonneg hB_nonneg)
  have hdrop_lower :
      (lam - lam ^ 2 * B) * mu ≤
        (N : ℝ) *
          ((1 - Real.exp (-(lam * B))) * (m / B)) := by
    calc
      (lam - lam ^ 2 * B) * mu =
          (lam * B - (lam * B) ^ 2) * ((N : ℝ) * (m / B)) := by
            field_simp [hB_pos.ne']
            ring
      _ ≤ (1 - Real.exp (-(lam * B))) * ((N : ℝ) * (m / B)) := by
            exact mul_le_mul_of_nonneg_right hq_lower hcoeff_nonneg
      _ = (N : ℝ) *
          ((1 - Real.exp (-(lam * B))) * (m / B)) := by
            ring
  have hchord :=
    targetLowerTailExponentialMoment_le_exp_chord
      (N := N) (rIn := rIn) (rOut := rOut) (T := T)
      target (lam := lam) hlam_nonneg
  have hchord_to_quad :
      Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) ≤
        Real.exp (lam * (T : ℝ) - (lam - lam ^ 2 * B) * mu) := by
    apply Real.exp_le_exp.mpr
    simpa [B, m, mu] using sub_le_sub_left hdrop_lower (lam * (T : ℝ))
  have hopt :
      Real.exp (lam * (T : ℝ) - (lam - lam ^ 2 * B) * mu) ≤
        Real.exp (-(gap ^ 2 / (4 * B * mu))) := by
    exact exp_chord_quadratic_optimized
      (T := (T : ℝ)) (gap := gap) (B := B) (mu := mu) (lam := lam)
      hB_pos hmu_pos' hgap (by simpa [mu, m] using hmean) rfl
  calc
    targetLowerTailExponentialMoment (N := N) rIn rOut T target
        (gap /
          (2 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))
        = targetLowerTailExponentialMoment (N := N) rIn rOut T target lam := by
          simp [lam, B, m, mu]
    _ ≤ Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := hchord
    _ ≤ Real.exp (lam * (T : ℝ) - (lam - lam ^ 2 * B) * mu) :=
          hchord_to_quad
    _ ≤ Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by
          simpa [B, m, mu, mul_assoc] using hopt
end PebblingLean.Hypercube
