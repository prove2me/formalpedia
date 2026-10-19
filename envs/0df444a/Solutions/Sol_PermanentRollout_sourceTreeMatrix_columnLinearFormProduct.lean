-- Prove2me | solution 1 for PermanentRollout.sourceTreeMatrix_columnLinearFormProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/6ff82b3b-1bdd-4e03-9117-745123bb8f57

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t d : ℕ) (hd : d ≤ t) (ζ : ℂ)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    columnLinearFormProduct
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves) =
      columnLinearFormProduct
        (treeLinearFormMatrix (sourceRowBlock b t) t d ζ tree) := by
  classical
  unfold columnLinearFormProduct
  refine Fintype.prod_equiv
    (finCongr
      (sourceTreeLinearFormVectors_length
        b t d hd ζ tree hnodup hleaves).symm)
    (fun column =>
      columnLinearForm
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves) column)
    (fun column =>
      columnLinearForm
        (treeLinearFormMatrix (sourceRowBlock b t) t d ζ tree) column)
    ?_
  intro column
  rfl
end PermanentRollout
