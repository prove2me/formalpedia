-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalRelNormCount.relNorm_eq_pow_primeRelNormExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:27:47.052351+00:00
-- url     : https://prove2.me/submissions/f6b151c6-5ea1-4d6a-9d48-b6f2c6e2dc39

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_LocalRelNormCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalRelNormCount
open UniqueFactorizationMonoid
variable (R S : Type*)
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
variable [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
namespace QEC.Coding.AlgebraicGeometry.LocalRelNormCount
theorem _root_.solution (P : Ideal S) (p : Ideal R)
    [P.LiesOver p] [p.IsPrime] :
    Ideal.relNorm R P = p ^ primeRelNormExponent R S P p :=
  Nat.find_spec (Ideal.exists_relNorm_eq_pow_of_isPrime P p)
end QEC.Coding.AlgebraicGeometry.LocalRelNormCount
