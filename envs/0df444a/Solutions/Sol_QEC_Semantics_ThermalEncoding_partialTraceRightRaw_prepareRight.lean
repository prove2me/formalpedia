-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.partialTraceRightRaw_prepareRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:13.067462+00:00
-- url     : https://prove2.me/submissions/80389275-0ec8-4c8f-b8f5-41b5653fb03c

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_prepareRight_apply_rankOne
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    partialTraceRightRaw H K (prepareRight H K sigma A) = A := by
  let basis := stdOrthonormalBasis Complex H
  rw [QuditSubsystem.operator_eq_sum_rankOne_basis H basis A, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [prepareRight_apply_rankOne, map_sum]
  calc
    (∑ j, partialTraceRightRaw H K
      (InnerProductSpace.rankOne Complex
        (A (basis i) ⊗ₜ[Complex] spectralEnsembleVector sigma j)
        (basis i ⊗ₜ[Complex] spectralEnsembleVector sigma j)).toLinearMap) =
        ∑ j, inner Complex (spectralEnsembleVector sigma j)
          (spectralEnsembleVector sigma j) •
            (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
              apply Finset.sum_congr rfl
              intro j _
              rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    _ = (∑ j, inner Complex (spectralEnsembleVector sigma j)
          (spectralEnsembleVector sigma j)) •
            (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
              rw [Finset.sum_smul]
    _ = (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
          rw [spectralEnsembleVector_sum_inner]
          simp
end QEC.Semantics.ThermalEncoding
