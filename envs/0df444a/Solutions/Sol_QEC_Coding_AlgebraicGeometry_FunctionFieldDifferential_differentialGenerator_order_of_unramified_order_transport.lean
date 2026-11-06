-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_unramified_order_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:04:54.72521+00:00
-- url     : https://prove2.me/submissions/9d69a63c-d658-4c13-be1d-069af8ca2cb0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_order_one_or_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
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
theorem _root_.solution
    (P : GlobalPlace k K) (Q : GlobalPlace k L)
    (horder : ∀ x : K, x ≠ 0 → Q.order (algebraMap K L x) = P.order x) :
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := L))
        functionFieldDifferentialGenerator_ne_zero =
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero := by
  have ht : P.uniformizer ≠ 0 := by
    intro hz
    have h := P.order_uniformizer
    rw [hz] at h
    simp [GlobalPlace.order] at h
  have htL : algebraMap K L P.uniformizer ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne ht
  have hQt : Q.order (algebraMap K L P.uniformizer) = 1 := by
    rw [horder P.uniformizer ht, P.order_uniformizer]
  obtain ⟨hdt, hP⟩ := differentialGenerator_order_of_order_one_or_neg_one
    P P.uniformizer ht (Or.inl P.order_uniformizer)
  obtain ⟨_, hQ⟩ := differentialGenerator_order_of_order_one_or_neg_one
    Q (algebraMap K L P.uniformizer) htL (Or.inl hQt)
  rw [hQ, hP, hQt, P.order_uniformizer, functionFieldDerivation_algebraMap,
    horder _ hdt]
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
