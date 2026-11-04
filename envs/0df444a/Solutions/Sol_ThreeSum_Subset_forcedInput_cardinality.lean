-- Prove2me | solution 1 for ThreeSum.Subset.forcedInput_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:20.050389+00:00
-- url     : https://prove2.me/submissions/86c2a304-6cbe-438a-9df2-eabef37e1d5e

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
theorem _root_.solution
    (f : Finset α → ℤ) (pre suffix : Finset α) (a : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hd : Disjoint pre suffix) :
    ∀ x, forcedInput f pre suffix x ≠ 0 → x.card = a - pre.card := by
  intro x hx
  have hxs : x ⊆ suffix := by
    by_contra h
    apply hx
    simp only [forcedInput, h, ite_false]
  have hfx : f (pre ∪ x) ≠ 0 := by
    simpa only [forcedInput, hxs, ite_true] using hx
  have hdx : Disjoint pre x := by
    apply Finset.disjoint_left.mpr
    intro b hbp hbx
    exact Finset.disjoint_left.mp hd hbp (hxs hbx)
  have hc := hf (pre ∪ x) hfx
  rw [Finset.card_union_of_disjoint hdx] at hc
  omega
end ThreeSum.Subset
