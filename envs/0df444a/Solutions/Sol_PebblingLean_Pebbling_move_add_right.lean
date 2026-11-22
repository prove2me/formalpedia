-- Prove2me | solution 1 for PebblingLean.Pebbling.move_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:39.600888+00:00
-- url     : https://prove2.me/submissions/a7dc000d-4f5f-4ac1-9420-ba065d14fdde

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
theorem _root_.solution [DecidableEq V] {G : Graph V} {D E A : Pebbling V}
    (hmove : Move G D E) :
    Move G (D + A) (E + A) := by
  rcases hmove with ⟨u, v, huv_adj, hD, rfl⟩
  have huv : u ≠ v := by
    intro h
    subst v
    exact (G.loopless u) huv_adj
  have hdist :
      moveDistribution (D + A) u v = moveDistribution D u v + A := by
    funext x
    by_cases hxu : x = u
    · subst x
      simp only [moveDistribution_apply_from, Pi.add_apply]
      calc
        D u + A u - 2 = A u + D u - 2 := by rw [Nat.add_comm]
        _ = A u + (D u - 2) := Nat.add_sub_assoc hD (A u)
        _ = D u - 2 + A u := by rw [Nat.add_comm]
    · by_cases hxv : x = v
      · subst x
        have hvu : v ≠ u := fun h => huv h.symm
        simp [moveDistribution, hvu]
        omega
      · simp [moveDistribution, hxu, hxv]
  refine ⟨u, v, huv_adj, ?_, hdist.symm⟩
  exact hD.trans (Nat.le_add_right (D u) (A u))
end PebblingLean.Pebbling
