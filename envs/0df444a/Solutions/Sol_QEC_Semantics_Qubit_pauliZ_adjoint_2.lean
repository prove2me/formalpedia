-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliZ_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:40:44.500804+00:00
-- url     : https://prove2.me/submissions/6dd3fb9b-fbb8-4b81-822c-5b2ffb76203e

-- ID: 411d90bf-e262-4d30-9563-ebafed5590bf | NAME: QEC.Semantics.Qubit.pauliZ_adjoint | 未本地编译验证
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
  have h : pauliZMatrix.conjTranspose = pauliZMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliZMatrix, zPhase, Complex.star_def]
  simpa [pauliZ, h] using
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := pauliZMatrix)).symm
