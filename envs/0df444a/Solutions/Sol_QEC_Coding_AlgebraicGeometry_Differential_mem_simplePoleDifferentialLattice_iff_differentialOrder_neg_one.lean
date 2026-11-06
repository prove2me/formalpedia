-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:48.588995+00:00
-- url     : https://prove2.me/submissions/2ff402f8-8cad-487f-af17-97d7836683f0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_uniformizer_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
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
    omega ∈ simplePoleDifferentialLattice P ↔
      -1 ≤ differentialOrder (k := k) (F := F) P omega homega := by
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  change (P.uniformizerInValuationRing : F) • omega ∈
      localDifferentialLattice P ↔
    -1 ≤ differentialOrder (k := k) (F := F) P omega homega
  rw [mem_localDifferentialLattice_iff_differentialOrder_nonnegative
    (k := k) (F := F) P ((P.uniformizerInValuationRing : F) • omega)
    (smul_ne_zero hpi homega)]
  rw [differentialOrder_uniformizer_smul (k := k) (F := F) P omega homega]
  omega
end QEC.Coding.AlgebraicGeometry.Differential
