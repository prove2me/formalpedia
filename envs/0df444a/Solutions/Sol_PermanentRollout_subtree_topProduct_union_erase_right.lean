-- Prove2me | solution 1 for PermanentRollout.subtree_topProduct_union_erase_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/89199aa5-b9c5-47c5-ac26-03cfcc7fadc8

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
    (y : ι → R) (t : ℕ) {i : ι} (hi : i ∈ right) :
    (∏ j ∈ (left ∪ right).erase i, y j ^ t) =
      (∏ j ∈ left, y j ^ t) *
        ∏ j ∈ right.erase i, y j ^ t := by
  have hnot : i ∉ left := fun h => (Finset.disjoint_left.mp hdisj) h hi
  have hdisj' : Disjoint left (right.erase i) :=
    Finset.disjoint_of_subset_right (Finset.erase_subset i right) hdisj
  rw [Finset.erase_union_distrib, Finset.erase_eq_self.mpr hnot]
  exact Finset.prod_union hdisj'
end PermanentRollout
