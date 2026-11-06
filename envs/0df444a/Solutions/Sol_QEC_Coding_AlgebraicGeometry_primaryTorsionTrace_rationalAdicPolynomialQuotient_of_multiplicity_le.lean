-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_rationalAdicPolynomialQuotient_of_multiplicity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:24.053467+00:00
-- url     : https://prove2.me/submissions/d23e0268-0ea5-42d1-83c1-4ba15f2a3ff7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_multiplicity_span_singleton_eq

section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
private theorem primaryTorsionTrace_cyclicQuotient_of_multiplicity_le_of_eq_span
    [IsNoetherianRing R] (P : Ideal R) [P.IsMaximal]
    (q a r : R) (hq : Irreducible q) (ha : a ≠ 0)
    (hP : P = Ideal.span {q}) (n : ℕ)
    (hPn : multiplicity P (Ideal.span {a}) ≤ n) :
    primaryTorsionTrace P (cyclicQuotientMul a r) n =
      (multiplicity P (Ideal.span {a}) : R ⧸ P) *
        Ideal.Quotient.mk P r := by
  subst P
  rw [multiplicity_span_singleton_eq q a hq ha] at hPn ⊢
  exact primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
    q a r hq ha n hPn
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (a : k[X]) (ha : a ≠ 0) (r : k[X]) (n : ℕ)
    (hpn : multiplicity p.asIdeal (Ideal.span {a}) ≤ n) :
    primaryTorsionTrace p.asIdeal (cyclicQuotientMul a r) n =
      (multiplicity p.asIdeal (Ideal.span {a}) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal r := by
  exact primaryTorsionTrace_cyclicQuotient_of_multiplicity_le_of_eq_span
    p.asIdeal (GlobalPlace.rationalAdicPolynomial p) a r
      (GlobalPlace.rationalAdicPolynomial_irreducible p) ha
        (GlobalPlace.rationalAdic_asIdeal_eq_span p) n hpn
end QEC.Coding.AlgebraicGeometry
