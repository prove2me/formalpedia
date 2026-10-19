-- Prove2me | solution 1 for PermanentRollout.exists_sourceTreeBlock_slicedGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/0c160a08-24d9-4577-8079-004c76666242

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceTreeBlockWeight_ne_zero
import Theorems.Thm_PermanentRollout_exists_sourceSeparatedBlockMinorSum_slicedGradient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤
      blockWidth d * blockColumns n d)
    (tree : BlockTree (Fin (blockCount n d)))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    ∃ (W : (Fin (sliceRank n d) → ℂ) →ₗ[ℂ]
          (Fin (blockVariables n d) → ℂ))
      (A : (Fin (blockVariables n d) → ℂ) →ₗ[ℂ]
          (Fin (sliceRank n d) → ℂ)),
      Function.Injective W ∧
      (∀ i : Fin (sliceRank n d),
        (slicedGradientPolynomial
          (sourceSeparatedBlockMinorSum n d
            (sourceTreeBlockWeight (blockCount n d) d tree)) W A i).IsHomogeneous
              (d - 1)) ∧
      (∀ u : Fin (sliceRank n d) → ℂ,
        (∀ i : Fin (sliceRank n d),
          MvPolynomial.eval u
            (slicedGradientPolynomial
              (sourceSeparatedBlockMinorSum n d
                (sourceTreeBlockWeight (blockCount n d) d tree)) W A i) = 0) ↔
                  u = 0) := by
  exact exists_sourceSeparatedBlockMinorSum_slicedGradient
    hd hn hscale (sourceTreeBlockWeight (blockCount n d) d tree)
    (sourceTreeBlockWeight_ne_zero (by omega) tree hnodup hleaves)
end PermanentRollout
