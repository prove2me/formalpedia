-- Prove2me | solution 1 for PebblingLean.Hypercube.mem_annulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:22.727984+00:00
-- url     : https://prove2.me/submissions/cd500fd9-d114-4a3e-b56e-7323062a1a7d

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ} {target center : HypercubeVertex n} :
    center ∈ annulus n rIn rOut target ↔
      rIn ≤ dist center target ∧ dist center target ≤ rOut := by
  simp [annulus]
end PebblingLean.Hypercube
