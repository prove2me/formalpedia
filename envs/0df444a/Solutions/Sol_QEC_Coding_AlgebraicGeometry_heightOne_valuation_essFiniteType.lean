-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOne_valuation_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:10.237045+00:00
-- url     : https://prove2.me/submissions/51f82f6c-d351-4a28-bae3-bc6529743094

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [IsDedekindDomain A] [IsFractionRing A K] [Algebra.EssFiniteType R A]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) :
    Algebra.EssFiniteType R T := by
  let S := H.valuationSubringAtPrime K
  let e : S ≃+* T := kaehlerValuationSubringEquiv S T heq
  let : Algebra A T := (e.toRingHom.comp (algebraMap A S)).toAlgebra
  let : IsLocalization H.asIdeal.primeCompl T :=
    (IsLocalization.isLocalization_iff_of_ringEquiv H.asIdeal.primeCompl e).mp inferInstance
  let : IsScalarTower R A T := .of_algebraMap_eq fun r => by
    apply Subtype.val_injective
    change (algebraMap R T r).val = (e (algebraMap A S (algebraMap R A r))).val
    calc
      _ = algebraMap T K (algebraMap R T r) := (hT _).symm
      _ = algebraMap R K r := (IsScalarTower.algebraMap_apply R T K r).symm
      _ = algebraMap A K (algebraMap R A r) := IsScalarTower.algebraMap_apply R A K r
      _ = _ := IsScalarTower.algebraMap_apply A S K _
  let : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T H.asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp R A T
end QEC.Coding.AlgebraicGeometry
