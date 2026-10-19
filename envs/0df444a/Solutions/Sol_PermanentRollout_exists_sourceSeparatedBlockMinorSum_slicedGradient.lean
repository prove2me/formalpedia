-- Prove2me | solution 1 for PermanentRollout.exists_sourceSeparatedBlockMinorSum_slicedGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/2b3b5d4a-345b-4f7e-b7dd-bad4eae1838f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceSeparatedBlockMinorSum_isHomogeneous
import Theorems.Thm_PermanentRollout_sourceSeparatedBlockMinorSum_criticalLocusDimension_le
import Theorems.Thm_PermanentRollout_exists_source_block_slicedGradient

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
    (weight : Fin (blockCount n d) → ℂ)
    (hw : ∀ h, weight h ≠ 0) :
    ∃ (W : (Fin (sliceRank n d) → ℂ) →ₗ[ℂ]
          (Fin (blockVariables n d) → ℂ))
      (A : (Fin (blockVariables n d) → ℂ) →ₗ[ℂ]
          (Fin (sliceRank n d) → ℂ)),
      Function.Injective W ∧
      (∀ i : Fin (sliceRank n d),
        (slicedGradientPolynomial
          (sourceSeparatedBlockMinorSum n d weight) W A i).IsHomogeneous
            (d - 1)) ∧
      (∀ u : Fin (sliceRank n d) → ℂ,
        (∀ i : Fin (sliceRank n d),
          MvPolynomial.eval u
            (slicedGradientPolynomial
              (sourceSeparatedBlockMinorSum n d weight) W A i) = 0) ↔
                u = 0) := by
  exact exists_source_block_slicedGradient hd hn hscale
    (sourceSeparatedBlockMinorSum n d weight)
    (sourceSeparatedBlockMinorSum_isHomogeneous n d weight)
    (sourceSeparatedBlockMinorSum_criticalLocusDimension_le hd weight hw)
end PermanentRollout
