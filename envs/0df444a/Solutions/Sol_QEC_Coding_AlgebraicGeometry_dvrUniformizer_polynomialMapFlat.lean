-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrUniformizer_polynomialMapFlat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:20.839212+00:00
-- url     : https://prove2.me/submissions/93868cbf-b19c-472e-bd63-638bc7edcec3

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrUniformizer_polynomialMapInjective

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) :
    (Polynomial.aeval π : Polynomial k →ₐ[k] V).toRingHom.Flat := by
  let : Algebra (Polynomial k) V := (Polynomial.aeval π).toRingHom.toAlgebra
  change (algebraMap (Polynomial k) V).Flat
  rw [RingHom.flat_algebraMap_iff]
  let : FaithfulSMul (Polynomial k) V :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (dvrUniformizer_polynomialMapInjective k V π hπ)
  infer_instance
end QEC.Coding.AlgebraicGeometry
