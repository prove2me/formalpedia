-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_multiplicity_tower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:55.098934+00:00
-- url     : https://prove2.me/submissions/fe628f9a-35a3-4fac-9830-fc74fbf87163

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower

set_option autoImplicit false
open Module
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B C : Type*)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [FaithfulSMul B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [P.IsPrime] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hp : p ≠ ⊥) :
    multiplicity Q (differentIdeal A C) =
      multiplicity Q (differentIdeal B C) +
        P.ramificationIdx' Q * multiplicity P (differentIdeal A B) := by
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  letI : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  have hP_ne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hQ_ne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hP_ne Q
  have hP_prime : Prime P := Ideal.prime_of_isPrime hP_ne inferInstance
  have hQ_prime : Prime Q := Ideal.prime_of_isPrime hQ_ne inferInstance
  have hAC_ne : differentIdeal A C ≠ ⊥ := differentIdeal_ne_bot
  have hBC_ne : differentIdeal B C ≠ ⊥ := differentIdeal_ne_bot
  have hAB_ne : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hAC_finite : FiniteMultiplicity Q (differentIdeal A C) :=
    FiniteMultiplicity.of_prime_left hQ_prime hAC_ne
  have hBC_finite : FiniteMultiplicity Q (differentIdeal B C) :=
    FiniteMultiplicity.of_prime_left hQ_prime hBC_ne
  have hAB_finite : FiniteMultiplicity P (differentIdeal A B) :=
    FiniteMultiplicity.of_prime_left hP_prime hAB_ne
  have hemultiplicity :
      emultiplicity Q (differentIdeal A C) =
        emultiplicity Q (differentIdeal B C) +
          P.ramificationIdx' Q * emultiplicity P (differentIdeal A B) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal A B C]
    rw [emultiplicity_mul hQ_prime]
    rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
      hAB_ne hP_prime.irreducible hQ_prime.irreducible hQ_ne]
  rw [hAC_finite.emultiplicity_eq_multiplicity,
    hBC_finite.emultiplicity_eq_multiplicity,
    hAB_finite.emultiplicity_eq_multiplicity] at hemultiplicity
  exact_mod_cast hemultiplicity
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
