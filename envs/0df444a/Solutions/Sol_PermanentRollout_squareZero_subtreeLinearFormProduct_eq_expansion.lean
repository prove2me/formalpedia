-- Prove2me | solution 1 for PermanentRollout.squareZero_subtreeLinearFormProduct_eq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/4b782327-a81f-44d9-973d-e70119fe0d43

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZeroBlockSum_pow_card_succ
import Theorems.Thm_PermanentRollout_subtreeLinearFormProduct_eq_expansion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (r : ℕ)
    (blocks : ι → Finset (Fin r)) (tree : BlockTree ι)
    (t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (hnodup : tree.leafList.Nodup)
    (hcard : ∀ i ∈ tree.leaves, (blocks i).card = t) :
    subtreeLinearFormProduct
        (fun i => squareZeroBlockSum r (blocks i)) t d ζ tree =
      ∑ i ∈ tree.leaves,
        algebraMap ℂ (SquareZeroAlgebra r)
            (subtreeCoefficient
              (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree i) *
          (squareZeroBlockSum r (blocks i) ^ (t - d) *
            ∏ j ∈ tree.leaves.erase i,
              squareZeroBlockSum r (blocks j) ^ t) := by
  apply subtreeLinearFormProduct_eq_expansion
    (fun i => squareZeroBlockSum r (blocks i)) t d hdpos hd hζ tree hnodup
  intro i hi
  simpa [hcard i hi] using squareZeroBlockSum_pow_card_succ r (blocks i)
end PermanentRollout
