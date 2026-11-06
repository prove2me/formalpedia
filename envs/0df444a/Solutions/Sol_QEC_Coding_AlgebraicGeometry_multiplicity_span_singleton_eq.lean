-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.multiplicity_span_singleton_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:21:59.639904+00:00
-- url     : https://prove2.me/submissions/15a39c5b-5287-46e5-b494-1d2a854adb70

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (q a : R) (hq : Irreducible q)
    (ha : a ≠ 0) :
    multiplicity (Ideal.span {q}) (Ideal.span {a}) = multiplicity q a := by
  have hqprime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanprime : Prime (Ideal.span {q}) := by
    rw [Ideal.prime_span_singleton_iff]
    exact hqprime
  have hspan_ne : Ideal.span {a} ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt ha
  have hfiniteElement : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  have hfiniteIdeal :
      FiniteMultiplicity (Ideal.span {q}) (Ideal.span {a}) :=
    FiniteMultiplicity.of_prime_left hspanprime hspan_ne
  apply Nat.cast_injective (R := ℕ∞)
  rw [← hfiniteIdeal.emultiplicity_eq_multiplicity,
    ← hfiniteElement.emultiplicity_eq_multiplicity,
    Ideal.emultiplicity_eq_emultiplicity_span]
end QEC.Coding.AlgebraicGeometry
