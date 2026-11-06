-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliX_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:49:44.693947+00:00
-- url     : https://prove2.me/submissions/367fcf5d-f455-4c0d-91ae-a4d63c7b29db

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u

theorem solution :
    LinearMap.trace Complex QubitSpace (pauliX * pauliZ) = 0 := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  simp [pauliX, pauliZ, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_mul, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    pauliXMatrix, pauliZMatrix, flipBit, zPhase]
