-- Prove2me | solution 1 for PermanentRollout.subtreeLinearFormProduct_eq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/cccb4dc7-5a4d-411c-8e3a-4d146c04898d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_subtreeLinearFormProduct_eq_subtreeFormProduct
import Theorems.Thm_PermanentRollout_subtreeFormProduct_eq_expansion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommRing R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup)
    (hnil : ∀ i ∈ tree.leaves, y i ^ (t + 1) = 0) :
    subtreeLinearFormProduct y t d ζ tree =
      ∑ i ∈ tree.leaves,
        algebraMap ℂ R
            (subtreeCoefficient
              (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree i) *
          (y i ^ (t - d) * ∏ j ∈ tree.leaves.erase i, y j ^ t) := by
  rw [subtreeLinearFormProduct_eq_subtreeFormProduct
    y t d hdpos hζ tree]
  exact subtreeFormProduct_eq_expansion y t d hd
    (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree hnodup hnil
end PermanentRollout
