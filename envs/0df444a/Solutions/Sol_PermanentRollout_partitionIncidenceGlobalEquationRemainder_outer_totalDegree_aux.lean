-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalEquationRemainder_outer_totalDegree_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/257581ef-dfc4-4f96-a828-f880a8daa94d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_incidenceUniversalPartitionDerivative_totalDegree
import Theorems.Thm_PermanentRollout_incidenceUniversalPartitionDerivative_homogeneousComponent
import Theorems.Thm_PermanentRollout_incidence_totalDegree_sub_homogeneousComponent_universal
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalEquationRemainder_lift_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (a : Fin s) (i : Fin t) :
    (partitionIncidenceGlobalColumnLift t s d
      (partitionIncidenceGlobalEquationRemainder t s d a i)).totalDegree ≤
      d - 2 := by
  rw [partitionIncidenceGlobalEquationRemainder_lift_eq,
    ← incidenceUniversalPartitionDerivative_homogeneousComponent]
  simpa [Nat.sub_sub] using
    (incidence_totalDegree_sub_homogeneousComponent_universal
      (incidenceUniversalPartitionDerivative d i
        (partitionIncidenceGlobalUniversalParameter t s d)
        (fun row : Fin t => (a, row)))
      (incidenceUniversalPartitionDerivative_totalDegree d i
        (partitionIncidenceGlobalUniversalParameter t s d)
        (fun row : Fin t => (a, row))))
end PermanentRollout
