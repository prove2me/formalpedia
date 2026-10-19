-- Prove2me | solution 1 for PermanentRollout.sourceTreeMatrix_alpha_eq_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/46b1d93f-ef94-4416-9838-04e4d09e8f22

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceTreeMatrix_quotient_prod
import Theorems.Thm_PermanentRollout_sourceBlockAlpha_eq_squareZeroCoefficient

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
    (hleaves : tree.leaves = Finset.univ)
    (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d) :
    sourceBlockAlpha (b * t) d
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves)
        omitted =
      squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (subtreeLinearFormProduct
          (fun h => squareZeroBlockSum (b * t) (sourceRowBlock b t h))
          t d ζ tree) := by
  rw [sourceBlockAlpha_eq_squareZeroCoefficient
    (sourceTreeMatrix b t d hd ζ tree hnodup hleaves)
    omitted homitted,
    sourceTreeMatrix_quotient_prod]
end PermanentRollout
