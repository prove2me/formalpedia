-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquivPrimePowerQuotient_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:51.675666+00:00
-- url     : https://prove2.me/submissions/ea291dcb-2ebb-4969-876d-a593935366b2

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (q : R) (hq : q ≠ 0) (e i : ℕ) (hi : i < e) (r : R) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
    primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi
        (Ideal.Quotient.mk (Ideal.span {q}) r) =
      Ideal.Quotient.mk (Ideal.span {q}) r •
        primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi 1 := by
  letI := primaryTorsionGradeModule
    (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
  rw [← map_smul]
  change primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi
      (Ideal.Quotient.mk (Ideal.span {q}) r) =
    primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi
      (Ideal.Quotient.mk (Ideal.span {q}) r • 1)
  rw [smul_eq_mul, mul_one]
end QEC.Coding.AlgebraicGeometry
