-- Prove2me | solution 1 for PebblingLean.Pebbling.weight_reaches_le_of_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:29.395144+00:00
-- url     : https://prove2.me/submissions/453d6e43-a614-4696-86a6-649e807e7f60

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
public import Theorems.Thm_PebblingLean_Pebbling_weight_move_le_of_dist

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
    (hreach : Reaches G D E)
    (hdist : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    weight dist E target ≤ weight dist D target := by
  unfold Reaches at hreach
  refine hreach.head_induction_on ?refl ?head
  · rfl
  · intro A B hmove _ ih
    exact ih.trans (weight_move_le_of_dist (G := G) (dist := dist)
      (target := target) hmove hdist)
end PebblingLean.Pebbling
