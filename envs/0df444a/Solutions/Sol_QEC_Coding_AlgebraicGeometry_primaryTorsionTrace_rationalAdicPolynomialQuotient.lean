-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_rationalAdicPolynomialQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:12.585993+00:00
-- url     : https://prove2.me/submissions/03fb5b44-ed2b-423f-b474-92fbc34eeed7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_multiplicity_span_singleton_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicQuotient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible

section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]
private theorem primaryTorsionTrace_cyclicQuotient_of_eq_span
    [IsNoetherianRing R] (P : Ideal R) [P.IsMaximal]
    (q a r : R) (hq : Irreducible q) (ha : a ≠ 0)
    (hP : P = Ideal.span {q}) :
    primaryTorsionTrace P (cyclicQuotientMul a r)
        (multiplicity P (Ideal.span {a})) =
      (multiplicity P (Ideal.span {a}) : R ⧸ P) *
        Ideal.Quotient.mk P r := by
  subst P
  rw [multiplicity_span_singleton_eq q a hq ha]
  exact primaryTorsionTrace_cyclicQuotient q a r hq ha
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (a : k[X]) (ha : a ≠ 0) (r : k[X]) :
    primaryTorsionTrace p.asIdeal (cyclicQuotientMul a r)
        (multiplicity p.asIdeal (Ideal.span {a})) =
      (multiplicity p.asIdeal (Ideal.span {a}) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal r := by
  exact primaryTorsionTrace_cyclicQuotient_of_eq_span p.asIdeal
    (GlobalPlace.rationalAdicPolynomial p) a r
      (GlobalPlace.rationalAdicPolynomial_irreducible p) ha
        (GlobalPlace.rationalAdic_asIdeal_eq_span p)
end QEC.Coding.AlgebraicGeometry
