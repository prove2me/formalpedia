-- Prove2me | solution 1 for ThreeSum.Subset.mobius_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:10.44343+00:00
-- url     : https://prove2.me/submissions/71c34633-1a14-4453-a0fb-f4347f65c92d

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    mobius f (insert a q) =
      mobius (fun s => f (insert a s)) q - mobius f q := by
  unfold mobius
  rw [Finset.sum_powerset_insert ha]
  have hleft :
      (∑ s ∈ q.powerset, (-1 : ℤ) ^ ((insert a q).card - s.card) * f s) =
      -(∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f s) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp hs)
    have hexp : (insert a q).card - s.card = (q.card - s.card) + 1 := by
      rw [Finset.card_insert_of_notMem ha]
      omega
    rw [hexp, pow_succ]
    ring
  have hright :
      (∑ s ∈ q.powerset,
        (-1 : ℤ) ^ ((insert a q).card - (insert a s).card) * f (insert a s)) =
      ∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f (insert a s) := by
    apply Finset.sum_congr rfl
    intro s hs
    have has : a ∉ s := fun h => ha ((Finset.mem_powerset.mp hs) h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem has,
      Nat.add_sub_add_right]
  rw [hleft, hright]
  ring
end ThreeSum.Subset
