-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.transported_norm_xAdic_to_original_infinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:47.173194+00:00
-- url     : https://prove2.me/submissions/00bd3d0a-760e-4912-9896-179e1c1b4509

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_xAdic_order_rationalInvolution_eq_rationalInfinity_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X

section
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped LaurentPolynomial Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
omit [Finite k] in
/-- The involution is self-inverse.  Fraction-ring extensionality reduces this
to the variable, where the two reciprocal operations cancel. -/
private theorem rationalInvolution_involutive (h : RatFunc k) :
    InverseAffinePlace.rationalInvolution k
      (InverseAffinePlace.rationalInvolution k h) = h := by
  let e := InverseAffinePlace.rationalInvolution k
  have hhom : e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
      RingHom.id (RatFunc k) := by
    apply IsFractionRing.ringHom_ext (A := k[X])
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa only [RingHom.comp_apply, RingHom.id_apply, map_add] using
          congrArg₂ (· + ·) hp hq
    | monomial n a =>
        have hC' : e (e (RatFunc.C a)) = RatFunc.C a := by
          change e (e (algebraMap k (RatFunc k) a)) = algebraMap k (RatFunc k) a
          rw [e.commutes, e.commutes]
        have hC : e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) =
            (algebraMap k[X] (RatFunc k)) (Polynomial.C a) := by
          simpa [← RatFunc.algebraMap_eq_C] using hC'
        have hX' : e (e RatFunc.X) = RatFunc.X := by
          rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
            InverseAffinePlace.rationalInvolution_X, inv_inv]
        have hX : e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) =
            (algebraMap k[X] (RatFunc k)) Polynomial.X := by
          simpa using hX'
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [RingHom.comp_apply, RingHom.id_apply, map_mul, map_pow]
        change e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) *
            e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) ^ n =
          (algebraMap k[X] (RatFunc k)) (Polynomial.C a) *
            (algebraMap k[X] (RatFunc k)) Polynomial.X ^ n
        rw [hC, hX]
  change (e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom) h = h
  rw [hhom]
  rfl
omit [Finite k] in
/-- Norm functoriality for the transported rational-coordinate algebra.  The
map equation is proved on all fractions from the involutivity above; it is
not an extra condition on a caller. -/
private theorem rationalInvolution_norm_transport (f : F) :
    letI : Algebra k⟮X⟯ F :=
      InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) k F
    InverseAffinePlace.rationalInvolution k
      (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f) =
        Algebra.norm k⟮X⟯ f := by
  letI : Algebra k⟮X⟯ F :=
    InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
  exact @Algebra.norm_eq_of_ringEquiv k⟮X⟯ k⟮X⟯ F _ _ _ oldRationalAlgebra
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F)
    (InverseAffinePlace.rationalInvolution k) (by
      ext h
      change InverseAffinePlace.transportedRationalMap
          (oldRationalAlgebra := oldRationalAlgebra) k F
          (InverseAffinePlace.rationalInvolution k h) =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) h
      change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (InverseAffinePlace.rationalInvolution k
            (InverseAffinePlace.rationalInvolution k h)) =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) h
      rw [rationalInvolution_involutive]) f
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped LaurentPolynomial Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
theorem _root_.solution (f : F) :
    letI : Algebra k⟮X⟯ F :=
      InverseAffinePlace.transportedRationalAlgebra k F
    GlobalPlace.order (xAdicPlace k) (Algebra.norm k⟮X⟯ f) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k)
        (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra k F
  rw [← rationalInvolution_norm_transport
    (oldRationalAlgebra := oldRationalAlgebra) k F]
  exact xAdic_order_rationalInvolution_eq_rationalInfinity_order k
    (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f)
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
