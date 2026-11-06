-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquivCyclicPowerFactorQuotient_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:53.289491+00:00
-- url     : https://prove2.me/submissions/36ff5c37-e974-49f3-bd33-7ec52781e88d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R) (hb : b ≠ 0)
    (i : ℕ) (hi : i < e) (r : R) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e * b}) (Ideal.span {q}) i
    primaryTorsionGradeEquivCyclicPowerFactorQuotient
        q hq e b hb i hi (Ideal.Quotient.mk (Ideal.span {q}) r) =
      Ideal.Quotient.mk (Ideal.span {q}) r •
        primaryTorsionGradeEquivCyclicPowerFactorQuotient
          q hq e b hb i hi 1 := by
  letI := primaryTorsionGradeModule
    (M := R ⧸ Ideal.span {q ^ e * b}) (Ideal.span {q}) i
  rw [← map_smul]
  change primaryTorsionGradeEquivCyclicPowerFactorQuotient
      q hq e b hb i hi (Ideal.Quotient.mk (Ideal.span {q}) r) =
    primaryTorsionGradeEquivCyclicPowerFactorQuotient
      q hq e b hb i hi (Ideal.Quotient.mk (Ideal.span {q}) r • 1)
  rw [smul_eq_mul, mul_one]
end QEC.Coding.AlgebraicGeometry
