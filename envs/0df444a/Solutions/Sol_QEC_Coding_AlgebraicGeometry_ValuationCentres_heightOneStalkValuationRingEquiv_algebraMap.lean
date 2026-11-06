-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ValuationCentres.heightOneStalkValuationRingEquiv_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:00.143191+00:00
-- url     : https://prove2.me/submissions/8c103ce3-f201-471f-b3ff-1de7010ea0ae

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.ValuationCentres
theorem _root_.solution
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) (a : R) :
    ((heightOneStalkValuationRingEquiv R H)
      (algebraMap R ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
        (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) a)).val = algebraMap R K a := by
  let : IsLocalization H.asIdeal.primeCompl
      ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
        (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) :=
    _root_.AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R
      (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)
  unfold heightOneStalkValuationRingEquiv
  change ((IsLocalization.algEquiv H.asIdeal.primeCompl
    ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
      (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R)) (H.valuationSubringAtPrime K))
    (algebraMap R _ a)).val = algebraMap R K a
  rw [AlgEquiv.commutes]
  rfl
end QEC.Coding.AlgebraicGeometry.ValuationCentres
