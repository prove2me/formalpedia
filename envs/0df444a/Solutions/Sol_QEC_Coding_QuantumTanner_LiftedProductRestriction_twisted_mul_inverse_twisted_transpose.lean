-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductRestriction.twisted_mul_inverse_twisted_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:23:55.333902+00:00
-- url     : https://prove2.me/submissions/e3cdaaf3-9ea8-4baa-b307-9da74378f6dc

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
noncomputable section
variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
theorem _root_.solution
    (h : Matrix I K F) (g : Matrix J K F) (s : K → G) :
    twistedMatrix h s * (twistedMatrix g (fun k => (s k)⁻¹)).transpose =
      scalarMatrix (G := G) (h * g.transpose) := by
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, twistedMatrix, scalarMatrix,
    MonoidAlgebra.single_mul_single, mul_inv_cancel]
  exact (map_sum (MonoidAlgebra.singleAddHom 1)
    (fun k => h i k * g j k) Finset.univ).symm
end QEC.Coding.QuantumTanner.LiftedProductRestriction
