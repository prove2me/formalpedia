-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_rationalEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:02:23.628478+00:00
-- url     : https://prove2.me/submissions/a95e20ec-08aa-4646-80ba-aa66c69fce19

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (e : RatFunc k ≃ₐ[k] K) (f : RatFunc k) :
    functionFieldDerivation (k := k) (e f) =
      e (functionFieldDerivation (k := k) f) *
        functionFieldDerivation (k := k) (e RatFunc.X) := by
  let D := functionFieldDerivation (k := k) (F := K)
  let Dr := functionFieldDerivation (k := k) (F := RatFunc k)
  let Dt : Derivation k (RatFunc k) (RatFunc k) :=
    { toLinearMap := e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap)
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        change e.symm (D (e (a * b))) =
          a * e.symm (D (e b)) + b * e.symm (D (e a))
        simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add,
          e.symm_apply_apply] }
  have h : Dt = e.symm (D (e RatFunc.X)) • Dr := by
    apply (RatFuncDerivation.rationalDerivationEquiv (k := k)
      (M := RatFunc k)).injective
    change e.symm (D (e RatFunc.X)) = e.symm (D (e RatFunc.X)) * Dr RatFunc.X
    rw [show Dr RatFunc.X = 1 from functionFieldDerivation_apply_X, mul_one]
  have hf := congrArg e (Derivation.congr_fun h f)
  change e (e.symm (D (e f))) = e (e.symm (D (e RatFunc.X)) * Dr f) at hf
  simpa only [e.apply_symm_apply, map_mul, mul_comm] using hf
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
