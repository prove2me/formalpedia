-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliX_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:14.455214+00:00
-- url     : https://prove2.me/submissions/d177571a-214d-4b0f-b524-29478bed8f8a

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliXMatrix_conjTranspose

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution : LinearMap.adjoint pauliX = pauliX := by
  change LinearMap.adjoint (Matrix.toEuclideanLin pauliXMatrix) =
    Matrix.toEuclideanLin pauliXMatrix
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint pauliXMatrix,
    pauliXMatrix_conjTranspose]
end QEC.Semantics.Qubit
