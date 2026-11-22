-- Prove2me | solution 1 for PebblingLean.Pebbling.weight_move_le_of_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:31.388627+00:00
-- url     : https://prove2.me/submissions/f9020c83-c29e-472f-9a69-d1ba1c542266

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
public import Theorems.Thm_PebblingLean_Pebbling_weight_moveDistribution_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D E : Pebbling V} {target : V}
    (hmove : Move G D E)
    (hdist : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    weight dist E target ≤ weight dist D target := by
  rcases hmove with ⟨u, v, huv_adj, hD, rfl⟩
  have huv : u ≠ v := by
    intro huv_eq
    subst v
    exact (G.loopless u) huv_adj
  exact weight_moveDistribution_le (dist := dist) (D := D) (u := u) (v := v)
    (target := target) huv hD (hdist huv_adj)
end PebblingLean.Pebbling
