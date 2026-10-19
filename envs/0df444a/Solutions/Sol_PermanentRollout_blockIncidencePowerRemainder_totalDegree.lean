-- Prove2me | solution 1 for PermanentRollout.blockIncidencePowerRemainder_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/9f1aae18-eeb4-43af-bc3d-1be3e7a3515d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_incidence_mvPolynomial_totalDegree_map_le
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalPowerRemainder_totalDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {b t s d : ℕ} (hd : 3 ≤ d)
    (coordinate : Fin b × (Fin s × Fin t)) :
    (blockIncidencePowerRemainder
      b t s d coordinate).totalDegree < d - 1 := by
  unfold blockIncidencePowerRemainder
  exact lt_of_le_of_lt
    ((MvPolynomial.totalDegree_rename_le _ _).trans
      (incidence_mvPolynomial_totalDegree_map_le _ _))
    (partitionIncidenceGlobalPowerRemainder_totalDegree hd coordinate.2)
end PermanentRollout
