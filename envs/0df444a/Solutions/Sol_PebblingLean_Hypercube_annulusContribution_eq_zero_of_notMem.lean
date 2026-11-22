-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusContribution_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:51.796802+00:00
-- url     : https://prove2.me/submissions/cb904249-1699-4a73-9ed6-8f9625432db7

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
    {target center : HypercubeVertex n}
    (hmem : center ∉ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 0 := by
  have hnot : ¬ (rIn ≤ dist center target ∧ dist center target ≤ rOut) := by
    simp_all
  simp [annulusContribution, hnot]
end PebblingLean.Hypercube
