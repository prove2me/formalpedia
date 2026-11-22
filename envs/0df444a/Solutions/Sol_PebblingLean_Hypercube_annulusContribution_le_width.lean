-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusContribution_le_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:21.795916+00:00
-- url     : https://prove2.me/submissions/3680e8bf-3916-4047-ac84-61c68359cb3c

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Hypercube.mem_annulus

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ (rOut - rIn) := by
  unfold annulusContribution
  by_cases h : rIn ≤ dist center target ∧ dist center target ≤ rOut
  · have hsub : rOut - dist center target ≤ rOut - rIn :=
      tsub_le_tsub_left h.1 rOut
    simpa [h] using Nat.pow_le_pow_right (by decide : 0 < 2) hsub
  · simp [h]
end PebblingLean.Hypercube
