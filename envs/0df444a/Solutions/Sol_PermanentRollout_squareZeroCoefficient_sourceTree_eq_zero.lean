-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_sourceTree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/0aa928bf-ffa7-46f1-80c2-2548f30ee38c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_sourceTree_expansion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ)
    (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d)
    (hnot : ∀ h : Fin b, ¬omitted ⊆ sourceRowBlock b t h) :
    squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (subtreeLinearFormProduct
          (fun h => squareZeroBlockSum (b * t) (sourceRowBlock b t h))
          t d ζ tree) = 0 := by
  rw [squareZeroCoefficient_sourceTree_expansion
    b t d hdpos hd hζ tree hnodup hleaves omitted homitted]
  apply Finset.sum_eq_zero
  intro h _
  simp [hnot h]
end PermanentRollout
