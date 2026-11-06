-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.detectableOnWithScalar_of_quadratic_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:55.543225+00:00
-- url     : https://prove2.me/submissions/67974b74-898f-4d59-8d9e-0616f7b44874

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    {C : QuantumCode (Qudit.QuditRegister q)} {A : Operator (Qudit.QuditRegister q)}
    {alpha : Complex}
    (hQuadratic : ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
      inner Complex x (A x) = alpha * inner Complex x x) :
    DetectableOnWithScalar C A alpha := by
  intro x hx y hy
  have hConjugateQuadratic (z : Qudit.QuditRegister q) (hz : z ∈ C.carrier) :
      inner Complex (A z) z = star alpha * inner Complex z z := by
    calc
      inner Complex (A z) z = star (inner Complex z (A z)) := by
        exact (inner_conj_symm (𝕜 := Complex) (A z) z).symm
      _ = star (alpha * inner Complex z z) := by rw [hQuadratic z hz]
      _ = star alpha * inner Complex z z := by simp
  have hAdd : x + y ∈ C.carrier := C.carrier.add_mem hx hy
  have hSub : x - y ∈ C.carrier := C.carrier.sub_mem hx hy
  have hIAdd : x + Complex.I • y ∈ C.carrier := C.carrier.add_mem hx
    (C.carrier.smul_mem Complex.I hy)
  have hISub : x - Complex.I • y ∈ C.carrier := C.carrier.sub_mem hx
    (C.carrier.smul_mem Complex.I hy)
  have hScalarQuadratic (z : Qudit.QuditRegister q) :
      inner Complex (((alpha • (1 : Operator (Qudit.QuditRegister q))) z)) z =
        star alpha * inner Complex z z := by
    simp [mul_comm]
  have hPolarized : inner Complex (A y) x =
      inner Complex (((alpha • (1 : Operator (Qudit.QuditRegister q))) y)) x := by
    rw [inner_map_polarization A x y,
      inner_map_polarization (alpha • (1 : Operator (Qudit.QuditRegister q))) x y]
    rw [hConjugateQuadratic (x + y) hAdd,
      hConjugateQuadratic (x - y) hSub,
      hConjugateQuadratic (x + Complex.I • y) hIAdd,
      hConjugateQuadratic (x - Complex.I • y) hISub,
      hScalarQuadratic (x + y), hScalarQuadratic (x - y),
      hScalarQuadratic (x + Complex.I • y), hScalarQuadratic (x - Complex.I • y)]
  calc
    inner Complex x (A y) = star (inner Complex (A y) x) := by
      exact (inner_conj_symm (𝕜 := Complex) x (A y)).symm
    _ = star (inner Complex (((alpha • (1 : Operator (Qudit.QuditRegister q))) y)) x) := by
      rw [hPolarized]
    _ = alpha * inner Complex x y := by simp [mul_comm]
end QEC.Semantics.QuditSubsystem
