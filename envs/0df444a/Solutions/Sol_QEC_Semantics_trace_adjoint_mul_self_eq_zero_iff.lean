-- Prove2me | solution 1 for QEC.Semantics.trace_adjoint_mul_self_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:36:39.100965+00:00
-- url     : https://prove2.me/submissions/aa155db3-10a0-4770-bbe1-1d86348668e0

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (A : Operator H) :
    LinearMap.trace Complex H (LinearMap.adjoint A * A) = 0 ↔ A = 0 := by
  let b := stdOrthonormalBasis Complex H
  rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis]
  rw [LinearMap.toMatrix_mul]
  rw [LinearMap.toMatrix_adjoint]
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
  exact (LinearMap.toMatrix b.toBasis b.toBasis).map_eq_zero_iff
end QEC.Semantics
