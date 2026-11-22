-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusContribution_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:51.276283+00:00
-- url     : https://prove2.me/submissions/35f44c1e-ac20-47bb-a78d-4e9c6787d21a

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
    (hmem : center ∈ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 2 ^ (rOut - dist center target) := by
  simp [annulusContribution, mem_annulus.mp hmem]
end PebblingLean.Hypercube
