-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_quadratic_simplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:05:45.594245+00:00
-- url     : https://prove2.me/submissions/da3b9333-3e80-4ee6-aa6d-00e6d34eeaac

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_order_one_or_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) K] [IsScalarTower k (RatFunc k) L]
    [IsScalarTower (RatFunc k) K L]
    [Algebra.IsSeparable (RatFunc k) K] [Algebra.IsSeparable (RatFunc k) L]
    [FiniteDimensional (RatFunc k) K] [FiniteDimensional (RatFunc k) L]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution [CharP L 2]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (e : ℕ)
    (horder : ∀ x : K, x ≠ 0 → Q.order (algebraMap K L x) = (e : ℤ) * P.order x)
    (a : K) (y : L) (ha : P.order a = -1) (hyorder : Q.order y = -1)
    (hy : y ^ 2 + y = algebraMap K L a) :
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := L))
        functionFieldDifferentialGenerator_ne_zero =
      (e : ℤ) * differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero + 2 * ((e : ℤ) - 1) := by
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz, GlobalPlace.order] at ha
  have hy0 : y ≠ 0 := by
    intro hz
    simp [hz, GlobalPlace.order] at hyorder
  obtain ⟨hda, hP⟩ := differentialGenerator_order_of_order_one_or_neg_one P a ha0 (Or.inr ha)
  obtain ⟨_, hQ⟩ := differentialGenerator_order_of_order_one_or_neg_one Q y hy0 (Or.inr hyorder)
  have hderiv : functionFieldDerivation (k := k) (F := L) y =
      algebraMap K L (functionFieldDerivation (k := k) (F := K) a) := by
    have h := congrArg (functionFieldDerivation (k := k) (F := L)) hy
    rw [map_add, Derivation.leibniz_pow] at h
    simpa only [Nat.cast_ofNat, nsmul_eq_mul, CharTwo.two_eq_zero, zero_mul,
      zero_smul, zero_add, functionFieldDerivation_algebraMap] using h
  rw [hQ, hP, hyorder, ha, hderiv, horder _ hda]
  ring
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
