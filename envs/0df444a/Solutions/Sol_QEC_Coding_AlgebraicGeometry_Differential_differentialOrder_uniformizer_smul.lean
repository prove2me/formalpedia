-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_uniformizer_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:22.381268+00:00
-- url     : https://prove2.me/submissions/daf65fbe-2cd5-4b5d-b614-b8c546e81280

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
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
    differentialOrder (k := k) (F := F) P
        ((P.uniformizerInValuationRing : F) • omega)
        (smul_ne_zero
          (by
            simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
              localParameter_ne_zero (k := k) (F := F) P)
          homega) =
      differentialOrder (k := k) (F := F) P omega homega + 1 := by
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr
      homega
  simp only [differentialOrder, map_smul, smul_eq_mul]
  rw [GlobalPlace.order_mul P hpi hcoordinate]
  change P.order P.uniformizer +
      P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
        localDerivativeLatticeGeneratorOrder (k := k) (F := F) P =
    P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
        localDerivativeLatticeGeneratorOrder (k := k) (F := F) P + 1
  rw [P.order_uniformizer]
  ring
end QEC.Coding.AlgebraicGeometry.Differential
