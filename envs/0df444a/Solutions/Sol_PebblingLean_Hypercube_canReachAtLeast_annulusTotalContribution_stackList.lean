-- Prove2me | solution 1 for PebblingLean.Hypercube.canReachAtLeast_annulusTotalContribution_stackList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:38.923806+00:00
-- url     : https://prove2.me/submissions/c096d4eb-30cb-4b08-8e21-d207491f7fc2

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Theorems.Thm_PebblingLean_Hypercube_canReachAtLeast_annulusContribution_single
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_annulusContribution_eq_zero_of_notMem
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_add
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_zero
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
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (centers : List (HypercubeVertex n)) :
    CanReachAtLeast (graph n)
      (stackListDistribution rOut centers) target
      (annulusTotalContribution rIn rOut target centers) := by
  induction centers with
  | nil =>
      exact Pebbling.canReachAtLeast_zero (graph n) (stackListDistribution rOut []) target
  | cons center centers ih =>
      have hhead :
          CanReachAtLeast (graph n)
            (Pebbling.single center (2 ^ rOut)) target
            (annulusContribution rIn rOut target center) := by
        by_cases hmem : center ∈ annulus n rIn rOut target
        · exact canReachAtLeast_annulusContribution_single hmem
        · rw [annulusContribution_eq_zero_of_notMem hmem]
          exact Pebbling.canReachAtLeast_zero (graph n)
            (Pebbling.single center (2 ^ rOut)) target
      have hsum := Pebbling.canReachAtLeast_add hhead ih
      simpa [stackListDistribution, annulusTotalContribution, Nat.add_assoc] using hsum
end PebblingLean.Hypercube
