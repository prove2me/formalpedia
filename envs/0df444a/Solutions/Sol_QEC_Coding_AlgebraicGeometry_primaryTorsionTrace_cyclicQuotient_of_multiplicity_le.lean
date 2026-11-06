-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:33.245249+00:00
-- url     : https://prove2.me/submissions/09df8754-2baf-4d44-b4f3-6512d4586314

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicPowerFactorQuotient

section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
private theorem primaryTorsionTrace_cyclicPowerFactorQuotient_stable
    [IsNoetherianRing R] (q : R) (hq : Prime q)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : ¬ q ∣ b) (r : R)
    (n : ℕ) (hen : e ≤ n) :
    primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) n =
      primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) e := by
  induction n, hen using Nat.le_induction with
  | base => rfl
  | succ n hen ih =>
      rw [primaryTorsionTrace, Finset.sum_range_succ,
        primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
          q hq e b hb n hen r,
        add_zero]
      exact ih
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] (q a r : R) (hq : Irreducible q)
    [hmax : (Ideal.span {q}).IsMaximal] (ha : a ≠ 0)
    (n : ℕ) (hqn : multiplicity q a ≤ n) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r) n =
      (multiplicity q a : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  have hfinite : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  obtain ⟨b, hfactor, hb⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  have hbne : b ≠ 0 := by
    intro hbzero
    apply ha
    rw [hfactor, hbzero, mul_zero]
  calc
    primaryTorsionTrace (Ideal.span {q})
        (cyclicQuotientMul a r) n =
      primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q (multiplicity q a) b r)
          (multiplicity q a) := by
            conv_lhs => rw [hfactor]
            exact primaryTorsionTrace_cyclicPowerFactorQuotient_stable
              q hq.prime (multiplicity q a) b hb r n hqn
    _ = _ := primaryTorsionTrace_cyclicPowerFactorQuotient
      q hq.ne_zero (multiplicity q a) b hbne r
end QEC.Coding.AlgebraicGeometry
