-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:24.780097+00:00
-- url     : https://prove2.me/submissions/595dfc43-ea53-4c0c-9a20-080dc339b34a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialOrder_eq_coordinate_sub_generatorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
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
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) (omega : Differential k F) (homega : omega ≠ 0) :
    omega ∈ localDifferentialLattice P ↔
      0 ≤ differentialOrder (k := k) (F := F) P omega homega := by
  let a : F := functionFieldDerivation (k := k) (F := F)
    (P.uniformizerInValuationRing : F)
  have ha := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (k := k) (F := F) P
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr
      homega
  rw [mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
    (k := k) (F := F) P omega, ha.2.2]
  simp only [hcoordinate, false_or]
  rw [differentialOrder_eq_coordinate_sub_generatorOrder
    (k := k) (F := F) P omega homega ha]
  omega
end QEC.Coding.AlgebraicGeometry.Differential
