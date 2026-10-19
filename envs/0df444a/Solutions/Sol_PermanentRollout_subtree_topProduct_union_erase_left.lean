-- Prove2me | solution 1 for PermanentRollout.subtree_topProduct_union_erase_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/a914c645-e567-4ce8-b019-94355cfe898a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (left right : Finset ι) (hdisj : Disjoint left right)
    (y : ι → R) (t : ℕ) {i : ι} (hi : i ∈ left) :
    (∏ j ∈ (left ∪ right).erase i, y j ^ t) =
      (∏ j ∈ left.erase i, y j ^ t) *
        ∏ j ∈ right, y j ^ t := by
  have hnot : i ∉ right := fun h => (Finset.disjoint_left.mp hdisj) hi h
  have hdisj' : Disjoint (left.erase i) right :=
    Finset.disjoint_of_subset_left (Finset.erase_subset i left) hdisj
  rw [Finset.erase_union_distrib, Finset.erase_eq_self.mpr hnot]
  exact Finset.prod_union hdisj'
end PermanentRollout
