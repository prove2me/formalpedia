-- Prove2me | solution 1 for PermanentRollout.flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/46462f22-11b5-4e2f-9603-99039ebacd61

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_separatedBlockCriticalCoordinateRing_ringKrullDim_le_incidence

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {b t s d : ℕ} (hd : 3 ≤ d)
    (weight : Fin b → ℂ) (hw : ∀ h, weight h ≠ 0)
    (hincidence :
      ringKrullDim (BlockIncidenceCoordinateRing b t s d) ≤
        ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞)) :
    criticalLocusDimension
      (flattenedSeparatedBlockMinorSum b t s d weight) ≤
        ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by
  unfold criticalLocusDimension
  calc
    ringKrullDim (criticalCoordinateRing
      (flattenedSeparatedBlockMinorSum b t s d weight)) =
        ringKrullDim
          (SeparatedBlockCriticalCoordinateRing
            b t s d weight) :=
      (separatedBlockCriticalFlattenEquiv
        b t s d weight).symm.toRingEquiv.ringKrullDim
    _ ≤ ringKrullDim (BlockIncidenceCoordinateRing b t s d) :=
      separatedBlockCriticalCoordinateRing_ringKrullDim_le_incidence
        b t s d weight hw (by omega)
    _ ≤ ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) :=
      hincidence
end PermanentRollout
