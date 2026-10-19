-- Prove2me | solution 1 for PermanentRollout.blockIncidence_ringKrullDim_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/77de2c47-6505-41ad-8615-3a5dc8213b7f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockIncidence_ringKrullDim_le_of_power_reductions
import Theorems.Thm_PermanentRollout_blockIncidencePowerRemainder_totalDegree
import Theorems.Thm_PermanentRollout_blockIncidencePowerRemainder_aeval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {b t s d : ℕ} (hd : 3 ≤ d) (ht : d ≤ t) :
    ringKrullDim (BlockIncidenceCoordinateRing b t s d) ≤
      ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by
  exact blockIncidence_ringKrullDim_le_of_power_reductions hd
    (blockIncidencePowerRemainder b t s d)
    (blockIncidencePowerRemainder_totalDegree hd)
    (blockIncidencePowerRemainder_aeval hd ht)
end PermanentRollout
