-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZ_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:38:05.777091+00:00
-- url     : https://prove2.me/submissions/313a89b4-8b28-4c4f-9474-8bbf0529eac3

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

theorem solution : LinearMap.adjoint pauliZ = pauliZ := by
  rw [pauliZ, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZMatrix, Matrix.conjTranspose]
