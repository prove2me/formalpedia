-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.count_spanSingleton_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:09.250848+00:00
-- url     : https://prove2.me/submissions/e1189690-315e-4b90-a40c-6d2709e55eb0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_spanSingleton_eq_affinePrincipalCoefficient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalCoefficient_eq_order
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
theorem _root_.solution (P : carrier k F) {f : F} (hf : f ≠ 0) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
      GlobalPlace.order (globalPlace k F P) f := by
  calc
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
        affinePrincipalCoefficient k F P (Units.mk0 f hf) :=
      count_spanSingleton_eq_affinePrincipalCoefficient k F P hf
    _ = GlobalPlace.order (globalPlace k F P) f := by
      simpa only [Units.val_mk0] using
        (affinePrincipalCoefficient_eq_order k F P (Units.mk0 f hf))
end QEC.Coding.AlgebraicGeometry.AffinePlace
