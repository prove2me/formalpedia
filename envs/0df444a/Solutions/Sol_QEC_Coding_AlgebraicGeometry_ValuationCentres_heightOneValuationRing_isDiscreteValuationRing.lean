-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ValuationCentres.heightOneValuationRing_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:01.036007+00:00
-- url     : https://prove2.me/submissions/95f689d1-e521-42a2-b6fd-8890b10e41ac

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
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) :
    IsDiscreteValuationRing (H.valuationSubringAtPrime K) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R H.ne_bot _
end QEC.Coding.AlgebraicGeometry.ValuationCentres
