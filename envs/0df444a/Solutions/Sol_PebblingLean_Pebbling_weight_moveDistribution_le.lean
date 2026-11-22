-- Prove2me | solution 1 for PebblingLean.Pebbling.weight_moveDistribution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:55.316834+00:00
-- url     : https://prove2.me/submissions/8c99833d-718e-487e-8de4-71ac6eab794f

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
public import Theorems.Thm_PebblingLean_Pebbling_weight_moveDistribution
public import Theorems.Thm_PebblingLean_Pebbling_unitWeight_le_two_mul_of_dist_le_succ

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] [DecidableEq V] (dist : V → V → ℕ)
    (D : Pebbling V) {u v target : V} (huv : u ≠ v) (hD : 2 ≤ D u)
    (hdist : dist u target ≤ dist v target + 1) :
    weight dist (moveDistribution D u v) target ≤ weight dist D target := by
  have hw := unitWeight_le_two_mul_of_dist_le_succ (dist := dist)
    (u := u) (v := v) (target := target) hdist
  rw [weight_moveDistribution (dist := dist) (D := D) (u := u) (v := v)
    (target := target) huv hD]
  linarith
end PebblingLean.Pebbling
