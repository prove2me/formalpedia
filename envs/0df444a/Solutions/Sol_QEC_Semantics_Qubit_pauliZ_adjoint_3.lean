-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliZ_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:37.82243+00:00
-- url     : https://prove2.me/submissions/540512a0-0b88-47b1-a50e-748edc144904

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliZMatrix_conjTranspose

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution : LinearMap.adjoint pauliZ = pauliZ := by
  change LinearMap.adjoint (Matrix.toEuclideanLin pauliZMatrix) =
    Matrix.toEuclideanLin pauliZMatrix
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint pauliZMatrix,
    pauliZMatrix_conjTranspose]
end QEC.Semantics.Qubit
