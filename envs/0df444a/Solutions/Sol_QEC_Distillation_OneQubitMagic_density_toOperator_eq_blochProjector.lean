-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.density_toOperator_eq_blochProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:52:53.761479+00:00
-- url     : https://prove2.me/submissions/19cac351-4dde-42fb-85eb-d122c54b7d6e

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    rho.toOperator = blochProjector (densityBloch rho) := by
  let b := EuclideanSpace.basisFun (Fin 2) Complex
  let M := LinearMap.toMatrix b.toBasis b.toBasis rho.toOperator
  have htrace : Matrix.trace M = 1 := by
    rw [← LinearMap.trace_eq_matrix_trace Complex b.toBasis]
    exact rho.trace_one
  have hherm : Matrix.conjTranspose M = M := by
    rw [← LinearMap.toMatrix_adjoint b b]
    exact congrArg (LinearMap.toMatrix b.toBasis b.toBasis)
      rho.positive.adjoint_eq
  have h00 := congrFun (congrFun hherm (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hherm (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hherm (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hherm (1 : Fin 2)) (1 : Fin 2)
  simp only [Matrix.conjTranspose_apply] at h00 h01 h10 h11
  have h00im : (M 0 0).im = 0 := by
    have h := congrArg Complex.im h00
    simp [RCLike.star_def] at h
    linarith
  have h11im : (M 1 1).im = 0 := by
    have h := congrArg Complex.im h11
    simp [RCLike.star_def] at h
    linarith
  have h10re : (M 1 0).re = (M 0 1).re := by
    have h := congrArg Complex.re h10
    simpa [RCLike.star_def] using h.symm
  have h10im : (M 1 0).im = -(M 0 1).im := by
    have h := congrArg Complex.im h10
    simpa [RCLike.star_def] using h.symm
  have htraceRe : (M 0 0).re + (M 1 1).re = 1 := by
    have h := congrArg Complex.re htrace
    simpa [Matrix.trace] using h
  have hXmatrix : LinearMap.toMatrix b.toBasis b.toBasis pauliX = pauliXMatrix := by
    simp [b, pauliX, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hYmatrix : LinearMap.toMatrix b.toBasis b.toBasis pauliY = pauliYMatrix := by
    simp [b, pauliY, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hZmatrix : LinearMap.toMatrix b.toBasis b.toBasis pauliZ = pauliZMatrix := by
    simp [b, pauliZ, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hx : LinearMap.trace Complex QubitSpace (pauliX * rho.toOperator) =
      M 1 0 + M 0 1 := by
    rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis,
      LinearMap.toMatrix_mul, hXmatrix]
    change Matrix.trace (pauliXMatrix * M) = _
    simp [Matrix.trace, Matrix.mul_apply, pauliXMatrix, flipBit]
  have hy : LinearMap.trace Complex QubitSpace (pauliY * rho.toOperator) =
      Complex.I * M 0 1 - Complex.I * M 1 0 := by
    rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis,
      LinearMap.toMatrix_mul, hYmatrix]
    change Matrix.trace (pauliYMatrix * M) = _
    simp [Matrix.trace, Matrix.mul_apply, pauliYMatrix]
    ring
  have hz : LinearMap.trace Complex QubitSpace (pauliZ * rho.toOperator) =
      M 0 0 - M 1 1 := by
    rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis,
      LinearMap.toMatrix_mul, hZmatrix]
    change Matrix.trace (pauliZMatrix * M) = _
    simp [Matrix.trace, Matrix.mul_apply, pauliZMatrix, zPhase]
    ring
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  ext i j
  fin_cases i <;> fin_cases j
  all_goals change M _ _ = _
  all_goals
    simp only [blochProjector, blochOperator, densityBloch, pauliOperator,
      map_smul, map_add, LinearMap.toMatrix_one]
  all_goals rw [hx, hy, hz]
  all_goals simp [hXmatrix, hYmatrix, hZmatrix, b,
    pauliXMatrix, pauliYMatrix, pauliZMatrix, flipBit, zPhase]
  all_goals apply Complex.ext <;> norm_num <;> linarith
end QEC.Distillation.OneQubitMagic
