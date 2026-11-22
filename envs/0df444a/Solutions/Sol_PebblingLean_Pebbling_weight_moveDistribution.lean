-- Prove2me | solution 1 for PebblingLean.Pebbling.weight_moveDistribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:08.901335+00:00
-- url     : https://prove2.me/submissions/c90aa9df-d22e-4a3b-ac23-12099e9e61d4

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
public import Theorems.Thm_PebblingLean_Pebbling_sum_moveDistribution_mul
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Pebbling.weight_zero

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] [DecidableEq V] (dist : V → V → ℕ)
    (D : Pebbling V) {u v target : V} (huv : u ≠ v) (hD : 2 ≤ D u) :
    weight dist (moveDistribution D u v) target
      = weight dist D target - 2 * unitWeight dist target u + unitWeight dist target v := by
  simpa [weight] using
    sum_moveDistribution_mul (D := D) (w := unitWeight dist target) (u := u) (v := v) huv hD
end PebblingLean.Pebbling
