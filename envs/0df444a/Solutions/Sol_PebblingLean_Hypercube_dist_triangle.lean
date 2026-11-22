-- Prove2me | solution 1 for PebblingLean.Hypercube.dist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:41.308256+00:00
-- url     : https://prove2.me/submissions/8a93b5e3-242b-4003-9fe9-f683c04d010d

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
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
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} (x y z : HypercubeVertex n) :
    dist x z ≤ dist x y + dist y z := by
  classical
  unfold dist
  apply (Finset.card_mono ?_).trans
  · exact Finset.card_union_le _ _
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases hxy : x i = y i
  · simp_all
  · simp_all
end PebblingLean.Hypercube
