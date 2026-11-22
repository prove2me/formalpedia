-- Prove2me | solution 1 for PebblingLean.Hypercube.bernsteinExponent_two_width_mul_T_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:32.370802+00:00
-- url     : https://prove2.me/submissions/88c5522f-2f67-433c-a873-6caace6818f7

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
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
    {delta T B : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2)
    (hT_pos : 0 < T) (hB_pos : 0 < B) :
    (delta ^ 2 * T) / (96 * B) ≤
      bernsteinExponent (2 * B * T) B (delta * T / 4) := by
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hden_pos : 0 < 2 * (2 * B * T + B * (delta * T / 4) / 3) := by
    have hBT_pos : 0 < B * T := mul_pos hB_pos hT_pos
    have hfactor_pos : 0 < 2 + delta / 12 := by nlinarith
    have hprod : 0 < 2 * (B * T) * (2 + delta / 12) := by positivity
    convert hprod using 1
    ring
  have hden_le : 2 * (2 * B * T + B * (delta * T / 4) / 3) ≤
      5 * B * T := by
    have hBT_nonneg : 0 ≤ B * T := (mul_pos hB_pos hT_pos).le
    have hdelta_div : delta / 6 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdelta_div hBT_nonneg
    nlinarith
  have hnum_nonneg : 0 ≤ (delta * T / 4) ^ 2 := sq_nonneg _
  have hmain :
      (delta * T / 4) ^ 2 / (5 * B * T) ≤
        (delta * T / 4) ^ 2 /
          (2 * (2 * B * T + B * (delta * T / 4) / 3)) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  have hcoarse :
      (delta ^ 2 * T) / (96 * B) ≤ (delta * T / 4) ^ 2 / (5 * B * T) := by
    have hB_ne : B ≠ 0 := ne_of_gt hB_pos
    have hT_ne : T ≠ 0 := ne_of_gt hT_pos
    field_simp [hB_ne, hT_ne]
    nlinarith [sq_nonneg delta, hT_pos, hB_pos]
  exact hcoarse.trans (by simpa [bernsteinExponent] using hmain)
end PebblingLean.Hypercube
