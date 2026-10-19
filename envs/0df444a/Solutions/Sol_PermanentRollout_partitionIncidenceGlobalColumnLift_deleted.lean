-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalColumnLift_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/19965745-74ef-40f1-8f6e-5012d7ef3ced

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (a : Fin s) (i : Fin t) (q : ℕ) :
    partitionIncidenceGlobalColumnLift t s d
      (MvPolynomial.rename
        (fun row : Fin t => (Sum.inr (a, row) : IncidenceCoordinate t s))
        (deletedCoordinateEsymmPolynomial t q i)) =
      MvPolynomial.map
        (algebraMap ℂ ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))
        (MvPolynomial.rename
          (fun row : Fin t => (a, row))
          (deletedCoordinateEsymmPolynomial t q i)) := by
  classical
  unfold partitionIncidenceGlobalColumnLift
    deletedCoordinateEsymmPolynomial
  rw [Finset.esymm_map_val]
  simp only [map_sum, map_prod, MvPolynomial.rename_X,
    MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, Sum.elim_inr]
end PermanentRollout
