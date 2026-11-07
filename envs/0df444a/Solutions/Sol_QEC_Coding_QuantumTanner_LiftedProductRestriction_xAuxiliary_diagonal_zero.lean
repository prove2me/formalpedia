-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.xAuxiliary_diagonal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:23:52.603659+00:00
-- url     : https://prove2.me/submissions/47c3cbf3-05d6-4974-8cb5-e57710411e79

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
    (hA HA : Matrix C A R) (gA GA : Matrix C' A R)
    (h0 : hA * gA.transpose = 0) (h1 : HA * GA.transpose = 0)
    (V0 V1 : Matrix C' D R) (c : C) (d : D) :
    xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1)
        (false, c) (false, d) = 0 ∧
      xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1)
        (true, c) (true, d) = 0 := by
  constructor
  · simp [xAuxiliary, ← Matrix.mul_assoc, h0]
  · simp [xAuxiliary, ← Matrix.mul_assoc, h1]
end QEC.Coding.QuantumTanner.LiftedProductRestriction
