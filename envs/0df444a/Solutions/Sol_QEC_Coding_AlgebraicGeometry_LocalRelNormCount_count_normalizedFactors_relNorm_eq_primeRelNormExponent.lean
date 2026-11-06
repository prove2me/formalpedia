-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalRelNormCount.count_normalizedFactors_relNorm_eq_primeRelNormExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:29:01.018005+00:00
-- url     : https://prove2.me/submissions/b1a77aed-6840-4d5c-be03-d5b7fe9d8ed6

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_LocalRelNormCount
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalRelNormCount_relNorm_eq_pow_primeRelNormExponent

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
      primeRelNormExponent R S P p := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  rw [relNorm_eq_pow_primeRelNormExponent R S P p,
    normalizedFactors_of_irreducible_pow hp.irreducible, normalize_eq,
    Multiset.count_replicate, if_pos rfl]
end QEC.Coding.AlgebraicGeometry.LocalRelNormCount
