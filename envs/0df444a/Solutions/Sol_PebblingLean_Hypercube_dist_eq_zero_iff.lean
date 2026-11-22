-- Prove2me | solution 1 for PebblingLean.Hypercube.dist_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:40.67354+00:00
-- url     : https://prove2.me/submissions/ff0ffe31-40fd-4d17-9f7b-3d27220e5e59

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
theorem _root_.solution {n : ℕ} {x y : HypercubeVertex n} :
    dist x y = 0 ↔ x = y := by
  constructor
  · intro hdist
    funext i
    by_contra hne
    have hempty :
        (Finset.univ.filter fun i : Fin n => x i ≠ y i) = ∅ := by
      exact Finset.card_eq_zero.mp hdist
    simp_all
  · simp_all
end PebblingLean.Hypercube
