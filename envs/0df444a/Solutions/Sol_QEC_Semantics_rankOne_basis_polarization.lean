-- Prove2me | solution 1 for QEC.Semantics.rankOne_basis_polarization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:21.851176+00:00
-- url     : https://prove2.me/submissions/bc1cc435-f2df-4968-b56c-9fa9fd219822

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
namespace QEC.Semantics
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (x y : H) :
    (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + y) (x + y)).toLinearMap +
        Complex.I • ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + Complex.I • y)
            (x + Complex.I • y)).toLinearMap) -
        ((1 + Complex.I) * (2 : Complex)⁻¹) •
          ((InnerProductSpace.rankOne Complex x x).toLinearMap +
            (InnerProductSpace.rankOne Complex y y).toLinearMap) := by
  ext z
  have hIhalf : Complex.I * (2 : Complex)⁻¹ * Complex.I = -(2 : Complex)⁻¹ := by
    calc
      Complex.I * (2 : Complex)⁻¹ * Complex.I = (2 : Complex)⁻¹ *
          (Complex.I * Complex.I) := by ring
      _ = -(2 : Complex)⁻¹ := by rw [Complex.I_mul_I]; ring
  have hIhalf_mul (a : Complex) :
      Complex.I * ((2 : Complex)⁻¹ * (Complex.I * a)) = -(2 : Complex)⁻¹ * a := by
    calc
      Complex.I * ((2 : Complex)⁻¹ * (Complex.I * a)) =
          (Complex.I * (2 : Complex)⁻¹ * Complex.I) * a := by ring
      _ = -(2 : Complex)⁻¹ * a := by rw [hIhalf]
  simp [InnerProductSpace.rankOne_apply, Complex.conj_I]
  simp only [smul_smul]
  rw [hIhalf_mul (inner Complex y z), hIhalf_mul (inner Complex x z),
    hIhalf_mul (Complex.I * inner Complex y z)]
  module
end QEC.Semantics
