-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.selected_groupAlgebra_auxiliary_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:25:33.329934+00:00
-- url     : https://prove2.me/submissions/408250ef-fc41-4f98-aad8-15fbdbbe7dce

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_selected_auxiliary_pointwise_disjoint
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_twisted_mul_inverse_twisted_transpose_eq_zero
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_scalar_mul_scalar_transpose_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
noncomputable section
variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]
omit [Fintype C] [Fintype D]
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
theorem _root_.solution
    (hA : Matrix C A F) (hB : Matrix D B F)
    (gA : Matrix C' A F) (gB : Matrix D' B F)
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra F G))
    (V0 V1 : Matrix C' D (MonoidAlgebra F G))
    (c : Bool × C) (d : Bool × D) :
    zAuxiliary (scalarMatrix hB) (twistedMatrix hB b)
        (U0 * twistedMatrix gB (fun k => (b k)⁻¹)) (U1 * scalarMatrix gB) c d = 0 ∨
      xAuxiliary (scalarMatrix hA) (twistedMatrix hA a)
        ((scalarMatrix gA).transpose * V0)
        ((twistedMatrix gA (fun k => (a k)⁻¹)).transpose * V1) c d = 0 := by
  have hDualA' : hA * gA.transpose = 0 := by
    have ht := congrArg Matrix.transpose hDualA
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using ht
  apply selected_auxiliary_pointwise_disjoint
  · exact scalar_mul_scalar_transpose_eq_zero hA gA hDualA'
  · exact twisted_mul_inverse_twisted_transpose_eq_zero hA gA a hDualA'
  · exact scalar_mul_scalar_transpose_eq_zero gB hB hDualB
  · simpa only [inv_inv] using
      twisted_mul_inverse_twisted_transpose_eq_zero gB hB (fun k => (b k)⁻¹) hDualB
end QEC.Coding.QuantumTanner.LiftedProductRestriction
