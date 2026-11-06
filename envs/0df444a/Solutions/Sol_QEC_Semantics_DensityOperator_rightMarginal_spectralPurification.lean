-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.rightMarginal_spectralPurification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:57.096207+00:00
-- url     : https://prove2.me/submissions/db7c6f45-5238-4fc4-9d5a-17a9b3a77044

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_rankOne_sum_sum
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
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
theorem _root_.solution (rho : DensityOperator H) :
    (rightMarginal (spectralPurification rho)).toOperator = rho.toOperator := by
  change partialTraceRightRaw H H (spectralPurification rho).toOperator = rho.toOperator
  rw [spectralPurification, pureDensity_toOperator]
  change partialTraceRightRaw H H
    ((InnerProductSpace.rankOne Complex
      (∑ i, ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) ⊗ₜ[Complex]
        rho.spectralEigenbasis i)
      (∑ j, ((Real.sqrt (rho.spectralEigenvalues j) : Complex) • rho.spectralEigenbasis j) ⊗ₜ[Complex]
        rho.spectralEigenbasis j)).toLinearMap) = rho.toOperator
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simpa [rho.spectralEigenbasis.inner_eq_ite] using rho.spectralDecomposition.symm
end QEC.Semantics.DensityOperator
