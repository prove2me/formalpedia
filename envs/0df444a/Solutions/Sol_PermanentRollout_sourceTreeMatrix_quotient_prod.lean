-- Prove2me | solution 1 for PermanentRollout.sourceTreeMatrix_quotient_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/fa6c090a-9b39-444a-9497-b7161aeb30cb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_treeLinearFormMatrix_quotient_prod
import Theorems.Thm_PermanentRollout_sourceTreeMatrix_columnLinearFormProduct

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
    Ideal.Quotient.mk (squareZeroIdeal (b * t))
        (columnLinearFormProduct
          (sourceTreeMatrix b t d hd ζ tree hnodup hleaves)) =
      subtreeLinearFormProduct
        (fun h => squareZeroBlockSum (b * t) (sourceRowBlock b t h))
        t d ζ tree := by
  rw [sourceTreeMatrix_columnLinearFormProduct
    b t d hd ζ tree hnodup hleaves,
    treeLinearFormMatrix_quotient_prod]
end PermanentRollout
