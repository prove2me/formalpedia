-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalEquationRemainder_lift_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/ef61771e-a16b-4fbf-9db4-baaa4db2d923

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalColumnLift_equation
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalColumnLift_deleted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (a : Fin s) (i : Fin t) :
    partitionIncidenceGlobalColumnLift t s d
      (partitionIncidenceGlobalEquationRemainder t s d a i) =
      incidenceUniversalPartitionDerivative d i
        (partitionIncidenceGlobalUniversalParameter t s d)
        (fun row : Fin t => (a, row)) -
      MvPolynomial.C
        (algebraMap ℂ ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ))
          (((-1 : ℂ) ^ (d - 1)) * ((d - 1).factorial : ℂ))) *
      MvPolynomial.map
        (algebraMap ℂ ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))
        (MvPolynomial.rename
          (fun row : Fin t => (a, row))
          (deletedCoordinateEsymmPolynomial t (d - 1) i)) := by
  unfold partitionIncidenceGlobalEquationRemainder
  rw [map_sub, map_mul, partitionIncidenceGlobalColumnLift_equation,
    partitionIncidenceGlobalColumnLift_deleted]
  congr 2
  simp [partitionIncidenceGlobalColumnLift]
end PermanentRollout
