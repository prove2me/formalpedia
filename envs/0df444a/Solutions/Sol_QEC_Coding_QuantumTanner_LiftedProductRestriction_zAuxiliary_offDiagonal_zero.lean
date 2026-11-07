-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.zAuxiliary_offDiagonal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:23:47.202173+00:00
-- url     : https://prove2.me/submissions/a2be69f1-e8de-437a-9e3d-97cf2017bdb9

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
omit [Fintype C] [Fintype D]
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
theorem _root_.solution
    (hB HB : Matrix D B R) (gB GB : Matrix D' B R)
    (h0 : gB * hB.transpose = 0) (h1 : GB * HB.transpose = 0)
    (U0 U1 : Matrix C D' R) (c : C) (d : D) :
    zAuxiliary hB HB (U0 * GB) (U1 * gB) (false, c) (true, d) = 0 ∧
      zAuxiliary hB HB (U0 * GB) (U1 * gB) (true, c) (false, d) = 0 := by
  constructor
  · simp [zAuxiliary, Matrix.mul_assoc, h1]
  · simp [zAuxiliary, Matrix.mul_assoc, h0]
end QEC.Coding.QuantumTanner.LiftedProductRestriction
