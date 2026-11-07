-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.twisted_mul_inverse_twisted_transpose_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:24:24.417304+00:00
-- url     : https://prove2.me/submissions/dc566aa5-fd5f-48be-9c1e-ac23f5ef0132

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_twisted_mul_inverse_twisted_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
noncomputable section
variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
theorem _root_.solution
    (h : Matrix I K F) (g : Matrix J K F) (s : K → G)
    (hzero : h * g.transpose = 0) :
    twistedMatrix h s * (twistedMatrix g (fun k => (s k)⁻¹)).transpose = 0 := by
  rw [twisted_mul_inverse_twisted_transpose, hzero]
  ext i j
  simp [scalarMatrix, twistedMatrix]
end QEC.Coding.QuantumTanner.LiftedProductRestriction
