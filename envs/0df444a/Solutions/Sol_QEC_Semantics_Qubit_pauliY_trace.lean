-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliY_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:25:42.764201+00:00
-- url     : https://prove2.me/submissions/b0a6231e-5097-479f-9059-edc1eb170ca8

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution : LinearMap.trace Complex QubitSpace pauliY = 0 := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliY, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.toMatrix_toLin]
  change Matrix.trace pauliYMatrix = 0
  simp [Matrix.trace, pauliYMatrix]
end QEC.Semantics.Qubit
