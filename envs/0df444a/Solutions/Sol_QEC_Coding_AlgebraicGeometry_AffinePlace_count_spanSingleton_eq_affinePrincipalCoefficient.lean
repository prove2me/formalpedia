-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.count_spanSingleton_eq_affinePrincipalCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:17.96341+00:00
-- url     : https://prove2.me/submissions/6ad4ea8b-63ff-4671-8e6f-c436418c90bf

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_45ffe40864_30
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (P : carrier k F)
    {f : F} (hf : f ≠ 0) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
      affinePrincipalCoefficient k F P (Units.mk0 f hf) := by
  classical
  let B : Type _ := affineRing k F
  let q := IsLocalization.sec B⁰ f
  have hspan : FractionalIdeal.spanSingleton B⁰ f =
      FractionalIdeal.spanSingleton B⁰
          ((algebraMap B F) (q.2 : B))⁻¹ * (Ideal.span {q.1} : Ideal B) := by
    have hq : IsLocalization.mk' F q.1 q.2 = f := by
      dsimp [q]
      exact IsLocalization.mk'_sec (M := B⁰) F f
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [← hq, IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  have hspan_ne_zero : FractionalIdeal.spanSingleton B⁰ f ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
  rw [FractionalIdeal.count_well_defined F P hspan_ne_zero hspan]
  change _ = -((P.valuationOfNeZeroToFun (Units.mk0 f hf)).toAdd)
  dsimp [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun, q]
  ring
end QEC.Coding.AlgebraicGeometry.AffinePlace
