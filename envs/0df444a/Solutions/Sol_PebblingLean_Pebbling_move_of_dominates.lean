-- Prove2me | solution 1 for PebblingLean.Pebbling.move_of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:36.771423+00:00
-- url     : https://prove2.me/submissions/e3972f26-e088-4524-922f-cb0ee653579a

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_mono

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D E D' : Pebbling V}
    (hmove : Move G D E) (hdom : Dominates D' D) :
    ∃ E' : Pebbling V, Move G D' E' ∧ Dominates E' E := by
  rcases hmove with ⟨u, v, huv_adj, hD, rfl⟩
  have huv : u ≠ v := by
    intro huv_eq
    subst v
    exact (G.loopless u) huv_adj
  refine ⟨moveDistribution D' u v, ?_, moveDistribution_mono huv hdom⟩
  exact ⟨u, v, huv_adj, (hD.trans (hdom u)), rfl⟩
end PebblingLean.Pebbling
