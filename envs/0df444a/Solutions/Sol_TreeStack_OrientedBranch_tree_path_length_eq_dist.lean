-- Prove2me | solution 1 for TreeStack.OrientedBranch.tree_path_length_eq_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:57:59.186745+00:00
-- url     : https://prove2.me/submissions/54864624-d66f-4bc2-b43c-6f6a60ba70db

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution {u v : V} (p : T.graph.Walk u v)
    (hp : p.IsPath) :
    p.length = T.graph.dist u v := by
  obtain ⟨q, hq, hqdist⟩ :=
    T.isTree.connected.exists_path_of_dist u v
  have hEq :
      (⟨p, hp⟩ : T.graph.Path u v) =
        ⟨q, hq⟩ :=
    T.isTree.isAcyclic.subsingleton_path u v |>.elim _ _
  have hpq : p = q := congrArg Subtype.val hEq
  rw [hpq, hqdist]
end TreeStack.OrientedBranch
