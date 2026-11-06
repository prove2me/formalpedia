-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_map_completedDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:43:43.084263+00:00
-- url     : https://prove2.me/submissions/4e159a81-d5a2-4373-90e7-3ffd07a903d5

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedIdeleDiagonal_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedIdeleAt_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedAdeleUnitsEquivIdele_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedDiagonal_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedDiagonal_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleDiagonal_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (u : Fˣ) :
    completedAdeleUnitsEquivIdele (k := k) (F := F)
        (Units.map (completedDiagonal (k := k) (F := F)).toMonoidHom u) =
      completedIdeleDiagonal (k := k) (F := F) u := by
  apply RestrictedProduct.ext
  intro P
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
