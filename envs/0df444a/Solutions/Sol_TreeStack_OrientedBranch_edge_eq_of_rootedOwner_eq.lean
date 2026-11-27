-- Prove2me | solution 1 for TreeStack.OrientedBranch.edge_eq_of_rootedOwner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:09:20.915395+00:00
-- url     : https://prove2.me/submissions/f11f12dd-7220-404d-9339-f4432d359d8c

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
import Theorems.Thm_TreeStack_OrientedBranch_rootedOther_adj_rootedOwner
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_dist_eq_rootedOther_add_one
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_other_edge
import Theorems.Thm_TreeStack_OrientedBranch_eq_of_adj_owner_of_dist

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (r : V) (B D : OrientedBranch T)
    (hOwner : B.rootedOwner r = D.rootedOwner r) :
    s(B.root, B.parent) = s(D.root, D.parent) := by
  have hOther :
      B.rootedOther r = D.rootedOther r := by
    apply eq_of_adj_owner_of_dist
      (T := T) r (B.rootedOwner r)
    · exact B.rootedOther_adj_rootedOwner r
    · rw [hOwner]
      exact D.rootedOther_adj_rootedOwner r
    · exact B.rootedOwner_dist_eq_rootedOther_add_one r
    · rw [hOwner]
      exact D.rootedOwner_dist_eq_rootedOther_add_one r
  calc
    s(B.root, B.parent) =
        s(B.rootedOwner r, B.rootedOther r) :=
      (B.rootedOwner_other_edge r).symm
    _ = s(D.rootedOwner r, D.rootedOther r) := by
      rw [hOwner, hOther]
    _ = s(D.root, D.parent) :=
      D.rootedOwner_other_edge r
end TreeStack.OrientedBranch
