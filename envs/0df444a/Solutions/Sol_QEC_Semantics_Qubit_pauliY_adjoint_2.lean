-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliY_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:31.789471+00:00
-- url     : https://prove2.me/submissions/82c04e06-f007-4350-9a8b-288ea77e50e9

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliYMatrix_conjTranspose

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution : LinearMap.adjoint pauliY = pauliY := by
  change LinearMap.adjoint (Matrix.toEuclideanLin pauliYMatrix) =
    Matrix.toEuclideanLin pauliYMatrix
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint pauliYMatrix,
    pauliYMatrix_conjTranspose]
end QEC.Semantics.Qubit
