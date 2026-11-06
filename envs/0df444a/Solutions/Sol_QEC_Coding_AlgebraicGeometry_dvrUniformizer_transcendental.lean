-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrUniformizer_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:43.77645+00:00
-- url     : https://prove2.me/submissions/b915c927-58a3-4fb3-9a20-f2b0f0abbaea

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) : Transcendental k π := by
  intro h
  exact hπ.not_isUnit ((isAlgebraic_iff_isIntegral.mp h).isUnit hπ.ne_zero)
end QEC.Coding.AlgebraicGeometry
