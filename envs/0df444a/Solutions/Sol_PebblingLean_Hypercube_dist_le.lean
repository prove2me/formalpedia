-- Prove2me | solution 1 for PebblingLean.Hypercube.dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:32.212003+00:00
-- url     : https://prove2.me/submissions/4427ae37-8887-409a-9476-cb3fa813167a

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
theorem _root_.solution {n : ℕ} (x y : HypercubeVertex n) : dist x y ≤ n := by
  unfold dist
  calc
    (Finset.univ.filter fun i : Fin n => x i ≠ y i).card ≤
        (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by
      simp
end PebblingLean.Hypercube
