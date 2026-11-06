-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:30.219171+00:00
-- url     : https://prove2.me/submissions/ef670ae8-498d-42db-9682-8f44432cacff

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicPowerFactorQuotient

section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]
private theorem primaryTorsionTrace_cyclicQuotient_of_eq_pow_mul
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (a r : R) (e : ℕ) (b : R) (hb : b ≠ 0)
    (hfactor : a = q ^ e * b) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r) e =
      (e : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  subst a
  exact primaryTorsionTrace_cyclicPowerFactorQuotient q hq e b hb r
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] (q a r : R) (hq : Irreducible q)
    [hmax : (Ideal.span {q}).IsMaximal] (ha : a ≠ 0) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r)
        (multiplicity q a) =
      (multiplicity q a : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  obtain ⟨b, hfactor⟩ := pow_multiplicity_dvd q a
  have hb : b ≠ 0 := by
    intro hb
    apply ha
    rw [hfactor, hb, mul_zero]
  exact primaryTorsionTrace_cyclicQuotient_of_eq_pow_mul
    q hq.ne_zero a r (multiplicity q a) b hb hfactor
end QEC.Coding.AlgebraicGeometry
