-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.card_lt_five_mul_permutationDistance_of_subtypeBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/b3079ef9-3064-41f7-b340-dce5a60973de

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_agreementSet_card_add_hammingDist

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) (hZ : Z.Nonempty)
    (p q : Equiv.Perm {x : V // x ∈ Z})
    (hbad : 5 * (subtypeBad Z E).card ≤ Fintype.card {x : V // x ∈ Z})
    (hseparated : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → p x ≠ q x) :
    Fintype.card {x : V // x ∈ Z} <
      5 * SoficGroups.permutationDistance p q := by
  have hagree :
      (SoficGroups.agreementSet p q).card ≤ (subtypeBad Z E).card := by
    apply Finset.card_le_card
    intro x hx
    have heq : p x = q x := (Finset.mem_filter.mp hx).2
    apply (mem_subtypeBad Z E x).2
    by_contra hnot
    exact hseparated x hnot heq
  have hpartition := SoficGroups.agreementSet_card_add_hammingDist p q
  change
    (SoficGroups.agreementSet p q).card +
        SoficGroups.permutationDistance p q =
      Fintype.card {x : V // x ∈ Z} at hpartition
  have hpositive : 0 < Fintype.card {x : V // x ∈ Z} := by
    simpa only [Fintype.card_coe] using hZ.card_pos
  omega
end SoficGroups.MatchedComponentCompletion
