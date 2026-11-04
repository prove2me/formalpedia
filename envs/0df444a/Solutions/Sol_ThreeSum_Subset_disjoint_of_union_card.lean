-- Prove2me | solution 1 for ThreeSum.Subset.disjoint_of_union_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:12.49117+00:00
-- url     : https://prove2.me/submissions/e81d186c-629c-43ef-8088-08625892f272

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
theorem _root_.solution {s v q : Finset α}
    (hu : s ∪ v = q) (hc : q.card = s.card + v.card) : Disjoint s v := by
  apply Finset.card_union_eq_card_add_card.mp
  simpa only [hu] using hc
end ThreeSum.Subset
