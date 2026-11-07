-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.unramifiedAt_of_localization_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:33:11.016602+00:00
-- url     : https://prove2.me/submissions/84c0a996-c59e-4bda-9822-143d07ce1800

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R C D : Type*} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra C D] [IsScalarTower R C D]
    (M : Submonoid C) [IsLocalization M D] [Algebra.FormallyUnramified R D]
    (q : Ideal C) [q.IsPrime] (hd : Disjoint (M : Set C) (q : Set C)) :
    Algebra.IsUnramifiedAt R q := by
  let Q := q.map (algebraMap C D)
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M D q inferInstance hd
  let instCQ : Algebra C (Localization.AtPrime Q) :=
    ((algebraMap D (Localization.AtPrime Q)).comp (algebraMap C D)).toAlgebra
  let : SMul C (Localization.AtPrime Q) := instCQ.toSMul
  let instDQ : Algebra D (Localization.AtPrime Q) := inferInstance
  let : SMul D (Localization.AtPrime Q) := instDQ.toSMul
  let : IsScalarTower C D (Localization.AtPrime Q) := .of_algebraMap_eq' rfl
  let : IsScalarTower R C (Localization.AtPrime Q) :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change algebraMap D (Localization.AtPrime Q) (algebraMap R D r) =
        algebraMap D (Localization.AtPrime Q) (algebraMap C D (algebraMap R C r))
      rw [IsScalarTower.algebraMap_apply R C D])
  let : Algebra.FormallyUnramified D (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_isLocalization Q.primeCompl
  let : Algebra.FormallyUnramified R (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.comp R D (Localization.AtPrime Q)
  exact Algebra.FormallyUnramified.of_equiv
    ((localizedPrimeAtPrimeEquiv (D := D) M q hd).restrictScalars R).symm
end QEC.Coding.AlgebraicGeometry
