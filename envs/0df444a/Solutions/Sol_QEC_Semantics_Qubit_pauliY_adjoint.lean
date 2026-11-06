-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliY_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:14:06.640382+00:00
-- url     : https://prove2.me/submissions/e9b918ed-2a9c-4570-a34b-f934c326c75e

-- ID: 131e9aef-3cf0-4d7b-b7c5-d1f84ab9252f | NAME: QEC.Semantics.Qubit.pauliY_adjoint | 未本地编译验证
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

theorem solution : LinearMap.adjoint pauliY = pauliY := by
  have h : pauliYMatrix.conjTranspose = pauliYMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliYMatrix, Complex.star_def]
  simpa [pauliY, h] using
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := pauliYMatrix)).symm
