-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_threshold_for_all_demands_of_minPile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:58:25.264826+00:00
-- url     : https://prove2.me/submissions/efa7b706-bb5b-47fd-98ff-c63c64cff5b1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_nonneg
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
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
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hmin :
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (minPile (splitM K n) : ℝ) *
          (((4 : ℝ) / 3) ^ splitA K n)) :
    ∀ t : ℕ, minPile (splitM K n) ≤ t →
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n) := by
  intro t ht
  let coeff : ℝ := (loss n / 2) * (((4 : ℝ) / 3) ^ splitA K n)
  have hloss_nonneg : 0 ≤ loss n := loss_nonneg n
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have ht_real : (minPile (splitM K n) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast ht
  have hmono : coeff * (minPile (splitM K n) : ℝ) ≤ coeff * (t : ℝ) :=
    mul_le_mul_of_nonneg_left ht_real hcoeff_nonneg
  have hmin' :
      (2 ^ rOut A K n : ℝ) ≤ coeff * (minPile (splitM K n) : ℝ) := by
    calc
      (2 ^ rOut A K n : ℝ)
          ≤ (loss n / 2) * (minPile (splitM K n) : ℝ) *
              (((4 : ℝ) / 3) ^ splitA K n) := hmin
      _ = coeff * (minPile (splitM K n) : ℝ) := by
          ring
  calc
    (2 ^ rOut A K n : ℝ) ≤ coeff * (minPile (splitM K n) : ℝ) := hmin'
    _ ≤ coeff * (t : ℝ) := hmono
    _ = (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n) := by
      simp [coeff, mul_comm, mul_assoc]
end PebblingLean.Hypercube.PaperParameters
