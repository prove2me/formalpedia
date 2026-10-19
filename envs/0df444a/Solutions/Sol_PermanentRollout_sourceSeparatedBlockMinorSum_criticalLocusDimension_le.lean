-- Prove2me | solution 1 for PermanentRollout.sourceSeparatedBlockMinorSum_criticalLocusDimension_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/8624bde1-057a-4cd7-adab-71996bd23bdd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_flattenedSeparatedBlockMinorSum_criticalLocusDimension_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d)
    (weight : Fin (blockCount n d) → ℂ)
    (hw : ∀ h, weight h ≠ 0) :
    criticalLocusDimension (sourceSeparatedBlockMinorSum n d weight) ≤
      ((blockCount n d *
        (powerSumParameter d + blockColumns n d * (d - 2)) : ℕ) :
          WithBot ℕ∞) := by
  have ht : d ≤ blockWidth d := by
    unfold blockWidth
    omega
  change
    criticalLocusDimension
      (flattenedSeparatedBlockMinorSum
        (blockCount n d) (blockWidth d) (blockColumns n d) d weight) ≤
      ((blockCount n d *
        ((2 ^ blockWidth d - 1) + blockColumns n d * (d - 2)) : ℕ) :
          WithBot ℕ∞)
  exact flattenedSeparatedBlockMinorSum_criticalLocusDimension_le
    hd ht weight hw
end PermanentRollout
