-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.permutationDistance_le_subtypeBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/336f3c5c-4b48-4b4b-aa6f-ec0b725536fd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (Z E : Finset V)
    (p q : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → p x = q x) :
    SoficGroups.permutationDistance p q ≤ (subtypeBad Z E).card := by
  unfold SoficGroups.permutationDistance hammingDist
  apply Finset.card_le_card
  intro x hx
  have hneq : p x ≠ q x := (Finset.mem_filter.mp hx).2
  apply (mem_subtypeBad Z E x).2
  by_contra hnot
  exact hneq (hagrees x hnot)
end SoficGroups.MatchedComponentCompletion
