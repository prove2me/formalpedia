-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.scalar_mul_scalar_transpose_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:24:52.776648+00:00
-- url     : https://prove2.me/submissions/a0962500-1326-4f9d-973a-5346a8f7a9ef

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_twisted_mul_inverse_twisted_transpose_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
noncomputable section
variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
theorem _root_.solution
    (h : Matrix I K F) (g : Matrix J K F) (hzero : h * g.transpose = 0) :
    scalarMatrix (G := G) h * (scalarMatrix (G := G) g).transpose = 0 := by
  simpa only [scalarMatrix, inv_one] using
    twisted_mul_inverse_twisted_transpose_eq_zero h g (fun _ => (1 : G)) hzero
end QEC.Coding.QuantumTanner.LiftedProductRestriction
