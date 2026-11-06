-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:30.919518+00:00
-- url     : https://prove2.me/submissions/29363fc9-9359-4419-ba81-4d1d3eb769ed

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionLayer_cyclicPowerFactorQuotient_stable
section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
private theorem primaryTorsionGrade_cyclicPowerFactorQuotient_subsingleton
    (q : R) (hq : Prime q) (e : ℕ) (b : R) (hb : ¬ q ∣ b)
    (i : ℕ) (hei : e ≤ i) :
    Subsingleton
      (primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i) := by
  rw [Submodule.Quotient.subsingleton_iff]
  apply eq_top_iff.mpr
  intro x _hx
  change (x : R ⧸ Ideal.span {q ^ e * b}) ∈
    primaryTorsionLayer (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e * b}) i
  rw [primaryTorsionLayer_cyclicPowerFactorQuotient_stable
      q hq e b hb i hei,
    ← primaryTorsionLayer_cyclicPowerFactorQuotient_stable
      q hq e b hb (i + 1) (hei.trans (Nat.le_succ i))]
  exact x.property
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] (q : R) (hq : Prime q)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : ¬ q ∣ b) (i : ℕ) (hei : e ≤ i)
    (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) i = 0 := by
  let p := Ideal.span {q}
  let M := R ⧸ Ideal.span {q ^ e * b}
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Subsingleton (primaryTorsionGrade p M i) :=
    primaryTorsionGrade_cyclicPowerFactorQuotient_subsingleton
      q hq e b hb i hei
  rw [primaryTorsionGradeTrace]
  have hend : primaryTorsionGradeEndomorphism p
      (cyclicPowerFactorQuotientMul q e b r) i = 0 :=
    Subsingleton.elim _ _
  rw [hend, map_zero]
end QEC.Coding.AlgebraicGeometry
