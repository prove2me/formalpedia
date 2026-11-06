-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliI_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:14:14.656636+00:00
-- url     : https://prove2.me/submissions/31e99fdb-e03a-4c8a-8c07-8f7e22007eac

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
theorem _root_.solution :
    LinearMap.trace Complex QubitSpace pauliI = (2 : Complex) := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliI, LinearMap.toMatrix_one]
  change Matrix.trace (1 : Matrix (Fin 2) (Fin 2) Complex) = 2
  simp [Matrix.trace]
end QEC.Semantics.Qubit
