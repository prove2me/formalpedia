-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalColumnLift_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/75c4467c-826b-4e19-9bc1-3cf74516c8c0

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (f : MvPolynomial (IncidenceCoordinate t s) ℂ) :
    letI := partitionIncidenceGlobalBaseAlgebra t s d
    MvPolynomial.aeval
      (fun coordinate : Fin s × Fin t =>
        Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
          (MvPolynomial.X (Sum.inr coordinate)))
      (partitionIncidenceGlobalColumnLift t s d f) =
      Ideal.Quotient.mk (partitionIncidenceIdeal t s d) f := by
  classical
  letI := partitionIncidenceGlobalBaseAlgebra t s d
  letI : IsScalarTower ℂ
      (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
      (PartitionIncidenceCoordinateRing t s d) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (partitionIncidenceGlobalBaseProjection t s d).commutes c |>.symm
  induction f using MvPolynomial.induction_on with
  | C c =>
      calc
        _ = algebraMap
            (MvPolynomial
              (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
            (PartitionIncidenceCoordinateRing t s d)
            (MvPolynomial.C c) := by
          simp [partitionIncidenceGlobalColumnLift]
        _ = Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
            (MvPolynomial.C c) := by
          change partitionIncidenceGlobalBaseProjection t s d
              (MvPolynomial.C c) = _
          simpa [partitionIncidenceGlobalBaseProjection] using
            (Ideal.Quotient.mk_algebraMap (R₁ := ℂ)
              (partitionIncidenceIdeal t s d) c).symm
  | add f g hf hg =>
      simp [map_add, hf, hg]
  | mul_X f coordinate hf =>
      calc
        _ = Ideal.Quotient.mk (partitionIncidenceIdeal t s d) f *
            MvPolynomial.aeval
              (fun coordinate : Fin s × Fin t =>
                Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
                  (MvPolynomial.X (Sum.inr coordinate)))
              (partitionIncidenceGlobalColumnLift t s d
                (MvPolynomial.X coordinate)) := by
          rw [map_mul, map_mul, hf]
        _ = Ideal.Quotient.mk (partitionIncidenceIdeal t s d) f *
              Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
                (MvPolynomial.X coordinate) := by
          apply congrArg
            (fun y : PartitionIncidenceCoordinateRing t s d =>
              Ideal.Quotient.mk (partitionIncidenceIdeal t s d) f * y)
          cases coordinate with
          | inl block =>
              rw [show partitionIncidenceGlobalColumnLift t s d
                    (MvPolynomial.X (Sum.inl block)) =
                  MvPolynomial.C (MvPolynomial.X (Sum.inl block)) by
                    simp [partitionIncidenceGlobalColumnLift],
                MvPolynomial.aeval_C]
              change partitionIncidenceGlobalBaseProjection t s d
                (MvPolynomial.X (Sum.inl block)) = _
              simp [partitionIncidenceGlobalBaseProjection]
          | inr coordinate =>
              simp [partitionIncidenceGlobalColumnLift]
        _ = Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
              (f * MvPolynomial.X coordinate) :=
          (map_mul (Ideal.Quotient.mk (partitionIncidenceIdeal t s d))
            f (MvPolynomial.X coordinate)).symm
end PermanentRollout
