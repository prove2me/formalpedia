-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.selected_auxiliary_pointwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:24:25.690015+00:00
-- url     : https://prove2.me/submissions/1904a0cf-2e45-497f-baca-fd125722239a

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_zAuxiliary_offDiagonal_zero
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_xAuxiliary_diagonal_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
omit [Fintype C] [Fintype D]
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
theorem _root_.solution
    (hA HA : Matrix C A R) (hB HB : Matrix D B R)
    (gA GA : Matrix C' A R) (gB GB : Matrix D' B R)
    (hA0 : hA * gA.transpose = 0) (hA1 : HA * GA.transpose = 0)
    (hB0 : gB * hB.transpose = 0) (hB1 : GB * HB.transpose = 0)
    (U0 U1 : Matrix C D' R) (V0 V1 : Matrix C' D R)
    (c : Bool × C) (d : Bool × D) :
    zAuxiliary hB HB (U0 * GB) (U1 * gB) c d = 0 ∨
      xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1) c d = 0 := by
  rcases c with ⟨s, c⟩
  rcases d with ⟨t, d⟩
  cases s <;> cases t
  · exact Or.inr (xAuxiliary_diagonal_zero hA HA gA GA hA0 hA1 V0 V1 c d).1
  · exact Or.inl (zAuxiliary_offDiagonal_zero hB HB gB GB hB0 hB1 U0 U1 c d).1
  · exact Or.inl (zAuxiliary_offDiagonal_zero hB HB gB GB hB0 hB1 U0 U1 c d).2
  · exact Or.inr (xAuxiliary_diagonal_zero hA HA gA GA hA0 hA1 V0 V1 c d).2
end QEC.Coding.QuantumTanner.LiftedProductRestriction
