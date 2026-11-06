-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliX_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:35:28.534192+00:00
-- url     : https://prove2.me/submissions/60dfdb5c-2922-425b-8577-fc649c750702

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

theorem solution : LinearMap.adjoint pauliX = pauliX := by
  rw [pauliX, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliXMatrix, Matrix.conjTranspose_apply, flipBit]
