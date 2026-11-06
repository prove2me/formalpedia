-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:25:46.037235+00:00
-- url     : https://prove2.me/submissions/ebe0c403-7c0e-469e-8189-76a8bf7b0269

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
theorem _root_.solution : LinearMap.trace Complex QubitSpace pauliZ = 0 := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliZ, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.toMatrix_toLin]
  change Matrix.trace pauliZMatrix = 0
  simp [Matrix.trace, pauliZMatrix, zPhase]
end QEC.Semantics.Qubit
