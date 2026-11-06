-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.tensorMap_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:22:00.960573+00:00
-- url     : https://prove2.me/submissions/1c999c60-0899-4ec9-9bde-ecc369069c4b

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
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
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K)
    (hA : LinearMap.IsPositive A) (hB : LinearMap.IsPositive B) :
    LinearMap.IsPositive (TensorProduct.map A B) := by
  have hAc : (LinearMap.toContinuousLinearMap A).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  have hBc : (LinearMap.toContinuousLinearMap B).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff B).mpr hB
  obtain ⟨m, a, ha⟩ :=
    ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hAc
  obtain ⟨n, b, hb⟩ :=
    ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hBc
  have ha' : A = ∑ i : Fin m,
      (InnerProductSpace.rankOne Complex (a i) (a i)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap ha
  have hb' : B = ∑ j : Fin n,
      (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hb
  rw [ha', hb', DensityOperator.tensorMap_sum_sum]
  apply LinearMap.isPositive_sum Finset.univ
  intro i _
  apply LinearMap.isPositive_sum Finset.univ
  intro j _
  rw [DensityOperator.tensorMap_rankOne]
  exact (InnerProductSpace.isPositive_rankOne_self
    (a i ⊗ₜ[Complex] b j)).toLinearMap
end QEC.Semantics.ThermalEncoding
