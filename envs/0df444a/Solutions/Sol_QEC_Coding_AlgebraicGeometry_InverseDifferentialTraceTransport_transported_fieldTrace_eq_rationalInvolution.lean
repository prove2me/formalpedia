-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.transported_fieldTrace_eq_rationalInvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:44:57.462505+00:00
-- url     : https://prove2.me/submissions/072b5844-63d1-4cdb-ba09-f72a3fdef20f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one


section
namespace QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
omit [Finite k] in
private theorem rationalInvolution_involutive (f : RatFunc k) :
    InverseAffinePlace.rationalInvolution k
      (InverseAffinePlace.rationalInvolution k f) = f := by
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
        have hC : e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) =
            (algebraMap k[X] (RatFunc k)) (Polynomial.C a) := by
          change e (e (algebraMap k (RatFunc k) a)) =
            algebraMap k (RatFunc k) a
          rw [e.commutes, e.commutes]
        have hX : e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) =
            (algebraMap k[X] (RatFunc k)) Polynomial.X := by
          change e (e RatFunc.X) = RatFunc.X
          rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
            InverseAffinePlace.rationalInvolution_X, inv_inv]
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [RingHom.comp_apply, RingHom.id_apply, map_mul, map_pow]
        change e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) *
            e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) ^ n =
          (algebraMap k[X] (RatFunc k)) (Polynomial.C a) *
            (algebraMap k[X] (RatFunc k)) Polynomial.X ^ n
        rw [hC, hX]
  change (e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom) f = f
  rw [hhom]
  rfl
end QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.directConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.directConstantScalarTower
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
omit [Finite k]
namespace QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
theorem _root_.solution (x : F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) k F
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Algebra.trace k⟮X⟯ F x =
      InverseAffinePlace.rationalInvolution k
        (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra x) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
    (oldPolynomialAlgebra := oldPolynomialAlgebra)
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) k F
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let e := InverseAffinePlace.rationalInvolution k
  have he : RingHom.comp (algebraMap k⟮X⟯ F) e.toRingEquiv.toRingHom =
      RingHom.comp (RingEquiv.refl F).toRingHom
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) := by
    ext f
    change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
        (e (e f)) =
      (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) f
    rw [rationalInvolution_involutive]
  have htrace := @Algebra.trace_eq_of_equiv_equiv
    k⟮X⟯ F k⟮X⟯ F _ _ _ _ oldRationalAlgebra inverseRationalAlgebra
      e.toRingEquiv (RingEquiv.refl F) he x
  calc
    Algebra.trace k⟮X⟯ F x =
        e (e.symm (Algebra.trace k⟮X⟯ F x)) :=
      (e.apply_symm_apply _).symm
    _ = e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra x) :=
      congrArg e htrace.symm
end QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
