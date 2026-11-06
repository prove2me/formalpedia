-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliX_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:41:46.7014+00:00
-- url     : https://prove2.me/submissions/e9e7c1c4-5049-4493-9486-99b94bf67b07

-- ID: 873880f0-de40-41a3-a7de-7f2d0782e7b0 | NAME: QEC.Semantics.Qubit.pauliX_adjoint | 未本地编译验证
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
  have h : pauliXMatrix.conjTranspose = pauliXMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliXMatrix, Complex.star_def, flipBit]
  simpa [pauliX, h] using
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := pauliXMatrix)).symm
