-- Prove2me | solution 1 for PebblingLean.Hypercube.solvableAtLeast_constantDistribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:25.096147+00:00
-- url     : https://prove2.me/submissions/b5963278-5887-4e2d-9b1b-4aa9ab9ddb0b

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
theorem _root_.solution (n S : ℕ) :
    SolvableAtLeast (graph n) (constantDistribution n S) S := by
  intro target
  exact ⟨constantDistribution n S, Relation.ReflTransGen.refl, by simp [constantDistribution]⟩
end PebblingLean.Hypercube
