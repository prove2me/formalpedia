-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_single_of_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:01.526093+00:00
-- url     : https://prove2.me/submissions/91561906-35ea-4743-b078-13528544064f

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_reaches_single_edge
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {u target : V}
    (walk : G.Walk u target) (T : ℕ) :
    CanReachAtLeast G (single u (T * 2 ^ walk.length)) target T := by
  induction walk with
  | nil v =>
      refine ⟨single v T, ?_, ?_⟩
      · simpa [Graph.Walk.length, Reaches] using
          (Relation.ReflTransGen.refl : Reaches G (single v T) (single v T))
      · simp
  | cons huv tail ih =>
      dsimp [Graph.Walk.length]
      let k := T * 2 ^ tail.length
      have hfirst : Reaches G (single _ (2 * k)) (single _ k) :=
        reaches_single_edge (G := G) huv k
      have hpow : T * 2 ^ (tail.length + 1) = 2 * k := by
        dsimp [k]
        rw [Nat.pow_succ]
        ac_rfl
      rcases ih with ⟨Dfinish, htail, htarget⟩
      exact ⟨Dfinish, by
        simpa [hpow, Reaches] using Relation.ReflTransGen.trans hfirst htail, htarget⟩
end PebblingLean.Pebbling
