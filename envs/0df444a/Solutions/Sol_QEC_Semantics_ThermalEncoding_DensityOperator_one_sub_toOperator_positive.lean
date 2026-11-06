-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.DensityOperator.one_sub_toOperator_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:12.49921+00:00
-- url     : https://prove2.me/submissions/dc24a961-50f5-4efe-85f7-cf77aa61eb7b

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_DensityOperator_spectralEigenvalues_le_one
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
open QEC.Semantics.ThermalEncoding.DensityOperator
namespace QEC.Semantics.ThermalEncoding.DensityOperator
theorem _root_.solution (rho : DensityOperator H) :
    LinearMap.IsPositive (1 - rho.toOperator) := by
  let b := rho.spectralEigenbasis
  have hid :
      (1 : Operator H) =
        ∑ i : Fin (Module.finrank Complex H),
          (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by
    change (LinearMap.id : Operator H) = _
    simpa using congrArg ContinuousLinearMap.toLinearMap
      (OrthonormalBasis.sum_rankOne_eq_id b).symm
  have hrho :
      rho.toOperator =
        ∑ i : Fin (Module.finrank Complex H),
          (rho.spectralEigenvalues i : Complex) •
            (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by
    ext x
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, b]
    apply Finset.sum_congr rfl
    intro i _
    change inner Complex (rho.positive.isSymmetric.eigenvectorBasis rfl i) x •
        rho.toOperator (rho.positive.isSymmetric.eigenvectorBasis rfl i) =
      (rho.positive.isSymmetric.eigenvalues rfl i : Complex) •
        (InnerProductSpace.rankOne Complex
          (rho.positive.isSymmetric.eigenvectorBasis rfl i)
          (rho.positive.isSymmetric.eigenvectorBasis rfl i)) x
    rw [rho.positive.isSymmetric.apply_eigenvectorBasis]
    simp only [InnerProductSpace.rankOne_apply, smul_smul]
    congr 1
    exact mul_comm _ _
  rw [hid, hrho, ← Finset.sum_sub_distrib]
  apply LinearMap.isPositive_sum Finset.univ
  intro i _
  have hcoeff : 0 ≤ (1 - rho.spectralEigenvalues i : Complex) := by
    exact_mod_cast sub_nonneg.mpr (spectralEigenvalues_le_one rho i)
  convert
    (InnerProductSpace.isPositive_rankOne_self (b i)).toLinearMap.smul_of_nonneg
      hcoeff using 1
  · simp [sub_smul]
end QEC.Semantics.ThermalEncoding.DensityOperator
