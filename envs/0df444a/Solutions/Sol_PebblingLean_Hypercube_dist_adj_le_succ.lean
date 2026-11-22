-- Prove2me | solution 1 for PebblingLean.Hypercube.dist_adj_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:08.346721+00:00
-- url     : https://prove2.me/submissions/e91930fd-098e-45b3-8fb0-5073ebcaa2af

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Theorems.Thm_PebblingLean_Hypercube_dist_triangle
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
theorem _root_.solution {n : ℕ} {x y t : HypercubeVertex n}
    (hxy : (graph n).Adj x y) : dist x t ≤ dist y t + 1 := by
  have h := dist_triangle x y t
  rw [hxy] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
end PebblingLean.Hypercube
