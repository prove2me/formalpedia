-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:33.540174+00:00
-- url     : https://prove2.me/submissions/7d1e57bb-54f0-443c-8630-bc624dfda6bb

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvr_formallySmoothCharZero

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (k A : Type*) [Field k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Algebra.Smooth k A := by
  let : Algebra.FinitePresentation k A :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := A)).mp inferInstance
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp
    (Set.eq_univ_iff_forall.mpr fun p ↦ ?_), inferInstance⟩
  change Algebra.FormallySmooth k (Localization.AtPrime p.asIdeal)
  let V := Localization.AtPrime p.asIdeal
  let : Algebra.EssFiniteType k V := Algebra.EssFiniteType.comp k A V
  by_cases hp : p.asIdeal = ⊥
  · have hf : IsField V := IsLocalRing.isField_iff_maximalIdeal_eq.mpr (by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      exact (congrArg (Ideal.map (algebraMap A V)) hp).trans (Ideal.map_bot))
    let : Field V := hf.toField
    exact Algebra.FormallySmooth.of_perfectField
  · let : IsDiscreteValuationRing V :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp V
    exact dvr_formallySmoothCharZero k V
end QEC.Coding.AlgebraicGeometry
