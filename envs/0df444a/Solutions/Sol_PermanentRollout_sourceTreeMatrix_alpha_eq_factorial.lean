-- Prove2me | solution 1 for PermanentRollout.sourceTreeMatrix_alpha_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/6ba75d83-61cb-4e32-9358-297b188ad421

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_sourceTree_eq_factorial
import Theorems.Thm_PermanentRollout_sourceTreeMatrix_alpha_eq_coefficient

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
    (homitted : omitted.card = d) (h : Fin b)
    (hsubset : omitted ⊆ sourceRowBlock b t h) :
    sourceBlockAlpha (b * t) d
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves)
        omitted =
      subtreeCoefficient
          (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h *
        (((t - d).factorial : ℕ) : ℂ) *
        (((t.factorial : ℕ) : ℂ) ^ (b - 1)) := by
  rw [sourceTreeMatrix_alpha_eq_coefficient
    b t d hd ζ tree hnodup hleaves omitted homitted,
    squareZeroCoefficient_sourceTree_eq_factorial
      b t d hdpos hd hζ tree hnodup hleaves
      omitted homitted h hsubset]
end PermanentRollout
