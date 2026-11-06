-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalRelNormCount.relNorm_prime_count_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:35.5385+00:00
-- url     : https://prove2.me/submissions/d2715434-3a4c-465e-8a8a-a6ff69fee125

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_LocalRelNormCount
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalRelNormCount_count_normalizedFactors_relNorm_eq_primeRelNormExponent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalRelNormCount
open UniqueFactorizationMonoid
variable (R S : Type*)
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
variable [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
namespace QEC.Coding.AlgebraicGeometry.LocalRelNormCount
theorem _root_.solution
    (P : Ideal S) (p : Ideal R) (hp0 : p ≠ ⊥)
    [P.LiesOver p] [p.IsPrime] :
    Multiset.count p (normalizedFactors (Ideal.relNorm R P)) =
      primeRelNormExponent R S P p :=
  count_normalizedFactors_relNorm_eq_primeRelNormExponent R S P p hp0
end QEC.Coding.AlgebraicGeometry.LocalRelNormCount
