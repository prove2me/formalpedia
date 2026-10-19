-- Prove2me | solution 1 for PermanentRollout.separatedBlockCriticalCoordinateRing_ringKrullDim_le_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/b11d5274-33ba-4cae-934d-7ca4bfd75e08

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockIncidenceWeightedCriticalGraph_surjective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (weight : Fin b → ℂ)
    (hw : ∀ h, weight h ≠ 0) (hd : 0 < d) :
    ringKrullDim (SeparatedBlockCriticalCoordinateRing
      b t s d weight) ≤
      ringKrullDim (BlockIncidenceCoordinateRing b t s d) :=
  ringKrullDim_le_of_surjective
    (blockIncidenceWeightedCriticalGraph
      b t s d weight hw hd).toRingHom
    (blockIncidenceWeightedCriticalGraph_surjective
      b t s d weight hw hd)
end PermanentRollout
