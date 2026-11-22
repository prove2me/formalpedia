-- Prove2me | solution 1 for PebblingLean.Pebbling.reaches_of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:01.85649+00:00
-- url     : https://prove2.me/submissions/428a0b68-584e-4739-8198-2779c2a72455

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_move_of_dominates

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D E D' : Pebbling V}
    (hreach : Reaches G D E) (hdom : Dominates D' D) :
    ∃ E' : Pebbling V, Reaches G D' E' ∧ Dominates E' E := by
  unfold Reaches at hreach
  refine hreach.head_induction_on
    (motive := fun A _ => ∀ D0 : Pebbling V, Dominates D0 A →
      ∃ E' : Pebbling V, Reaches G D0 E' ∧ Dominates E' E) ?refl ?head D' hdom
  · intro D0 hdom_E
    exact ⟨D0, Relation.ReflTransGen.refl, hdom_E⟩
  · intro A B hmove hreach_B _ih D0 hdom_A
    rcases move_of_dominates hmove hdom_A with ⟨B', hmove', hdom_B⟩
    rcases _ih B' hdom_B with ⟨E', hreach', hdom_E⟩
    exact ⟨E', Relation.ReflTransGen.head hmove' hreach', hdom_E⟩
end PebblingLean.Pebbling
