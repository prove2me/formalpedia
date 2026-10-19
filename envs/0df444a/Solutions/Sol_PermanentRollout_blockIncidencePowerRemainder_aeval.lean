-- Prove2me | solution 1 for PermanentRollout.blockIncidencePowerRemainder_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/ece1f233-644d-434c-b09a-db8749afa13b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalPowerRemainder_aeval
import Theorems.Thm_PermanentRollout_blockIncidenceSingleBlockInclusion_mk
import Theorems.Thm_PermanentRollout_blockIncidenceBaseProjection_comm

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {b t s d : ℕ} (hd : 3 ≤ d) (ht : d ≤ t)
    (coordinate : Fin b × (Fin s × Fin t)) :
    letI := blockIncidenceBaseAlgebra b t s d
    (Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
      (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2))) ^ (d - 1) =
      MvPolynomial.aeval
        (fun row : Fin b × (Fin s × Fin t) =>
          Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
            (MvPolynomial.X (row.1, Sum.inr row.2)))
        (blockIncidencePowerRemainder b t s d coordinate) := by
  classical
  letI := blockIncidenceBaseAlgebra b t s d
  letI := partitionIncidenceGlobalBaseAlgebra t s d
  let φ := blockIncidenceSingleBlockInclusion b t s d coordinate.1
  have hcoeff
      (p : MvPolynomial
        (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ) :
      algebraMap
        (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
        (BlockIncidenceCoordinateRing b t s d)
        (blockIncidenceBaseRename b t s d coordinate.1 p) =
      φ (algebraMap
        (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
        (PartitionIncidenceCoordinateRing t s d) p) := by
    change
      blockIncidenceBaseProjection b t s d
        ((MvPolynomial.rename
          (fun z : IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2)) =>
            (coordinate.1, z))) p) =
      φ (partitionIncidenceGlobalBaseProjection t s d p)
    exact DFunLike.congr_fun
      (blockIncidenceBaseProjection_comm b t s d coordinate.1) p
  have hpoly
      (p : MvPolynomial (Fin s × Fin t)
        (MvPolynomial
          (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)) :
      MvPolynomial.aeval
        (fun row : Fin b × (Fin s × Fin t) =>
          Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
            (MvPolynomial.X (row.1, Sum.inr row.2)))
        (MvPolynomial.rename
          (fun row : Fin s × Fin t => (coordinate.1, row))
          (MvPolynomial.map
            (blockIncidenceBaseRename b t s d coordinate.1) p)) =
      φ (MvPolynomial.aeval
        (fun row : Fin s × Fin t =>
          Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
            (MvPolynomial.X (Sum.inr row))) p) := by
    induction p using MvPolynomial.induction_on with
    | C p =>
        simpa using hcoeff p
    | add p q hp hq =>
        simp [hp, hq]
    | mul_X p row hp =>
        simp [hp, φ, blockIncidenceSingleBlockInclusion_mk]
  have hsource := congrArg φ
    (partitionIncidenceGlobalPowerRemainder_aeval hd ht coordinate.2)
  rw [map_pow] at hsource
  rw [blockIncidenceSingleBlockInclusion_mk] at hsource
  simp only [MvPolynomial.rename_X] at hsource
  rw [← hpoly] at hsource
  exact hsource
end PermanentRollout
