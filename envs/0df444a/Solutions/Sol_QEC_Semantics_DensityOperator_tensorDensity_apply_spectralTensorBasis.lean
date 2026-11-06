-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.tensorDensity_apply_spectralTensorBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:30.168382+00:00
-- url     : https://prove2.me/submissions/1e55b469-9fdc-4722-9bf6-d7fd74ed0bfe

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K)
    (i : Fin (Module.finrank Complex H)) (j : Fin (Module.finrank Complex K)) :
    (tensorDensity rho sigma).toOperator
        (rho.spectralEigenbasis i ⊗ₜ[Complex] sigma.spectralEigenbasis j) =
      ((rho.spectralEigenvalues i * sigma.spectralEigenvalues j : Real) : Complex) •
        (rho.spectralEigenbasis i ⊗ₜ[Complex] sigma.spectralEigenbasis j) := by
  rw [tensorDensity_toOperator, TensorProduct.map_tmul]
  unfold spectralEigenbasis spectralEigenvalues
  rw [rho.positive.isSymmetric.apply_eigenvectorBasis,
    sigma.positive.isSymmetric.apply_eigenvectorBasis]
  rw [TensorProduct.smul_tmul, smul_smul, TensorProduct.tmul_smul]
  norm_cast
end QEC.Semantics.DensityOperator
