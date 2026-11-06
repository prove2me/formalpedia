-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrUniformizer_polynomialMapInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:56:41.10944+00:00
-- url     : https://prove2.me/submissions/3c56ef87-8263-44fd-9872-41612754cadb

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrUniformizer_transcendental

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) :
    Function.Injective (Polynomial.aeval π : Polynomial k →ₐ[k] V) := by
  exact transcendental_iff_injective.mp
    (dvrUniformizer_transcendental k V π hπ)
end QEC.Coding.AlgebraicGeometry
