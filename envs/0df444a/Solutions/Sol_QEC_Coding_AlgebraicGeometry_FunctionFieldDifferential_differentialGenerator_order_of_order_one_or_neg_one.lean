-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_order_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:03:06.049254+00:00
-- url     : https://prove2.me/submissions/ba7b4d10-4067-42b7-82e8-36c09de3c2ee

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_logarithmicDifferential_order_of_order_one_or_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialOrder_eq_coordinate_sub_generatorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
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
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    ∃ _hdf : functionFieldDerivation (k := k) f ≠ 0,
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero =
          P.order f - 1 - P.order (functionFieldDerivation (k := k) f) := by
  let omega := Differential.logarithmicDifferential (k := k) f
  let homega := logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder
  have hlog := logarithmicDifferential_order_of_order_one_or_neg_one P f hf horder
  have hc : functionFieldDifferentialCoordinate (k := k) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff omega).mpr homega
  have hcoord : functionFieldDifferentialCoordinate (k := k) omega =
      f⁻¹ * functionFieldDerivation (k := k) f := by
    dsimp only [omega]
    rw [Differential.logarithmicDifferential, map_smul,
      functionFieldDifferentialCoordinate_differential]
    rfl
  have hdf : functionFieldDerivation (k := k) f ≠ 0 := by
    intro hz
    exact hc (by rw [hcoord, hz, mul_zero])
  refine ⟨hdf, ?_⟩
  have hcutoff := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff (k := k) P
  change differentialOrder P omega homega = -1 at hlog
  rw [differentialOrder_eq_coordinate_sub_generatorOrder P omega homega hcutoff,
    hcoord, P.order_mul (inv_ne_zero hf) hdf, P.order_inv] at hlog
  have hone : P.order (1 : K) = 0 := by
    simpa using P.order_algebraMap (1 : k) one_ne_zero
  rw [differentialOrder_eq_coordinate_sub_generatorOrder P
    (functionFieldDifferentialGenerator (k := k) (F := K))
    functionFieldDifferentialGenerator_ne_zero hcutoff,
    functionFieldDifferentialCoordinate_generator, hone]
  omega
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
