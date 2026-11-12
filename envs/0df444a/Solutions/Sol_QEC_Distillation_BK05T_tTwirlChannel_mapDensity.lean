-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirlChannel_mapDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:22:08.555204+00:00
-- url     : https://prove2.me/submissions/df075cea-b111-4b80-afaa-570cdd56a01d

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem tTwirlKraus_branch (i : Fin 3) (A : Operator QubitSpace) :
    (tTwirlKraus.operator i).comp
        (A.comp (LinearMap.adjoint (tTwirlKraus.operator i))) =
      (1 / 3 : Complex) • (tTwirlUnitary i).conjOperator A := by
  unfold tTwirlKraus tTwirlKrausUnscaled
  rw [FiniteKrausFamily.scale_operator]
  have hAdj : LinearMap.adjoint
      (tTwirlAmplitude • (tTwirlUnitary i).toLinearEquiv.toLinearMap) =
      star tTwirlAmplitude •
        LinearMap.adjoint (tTwirlUnitary i).toLinearEquiv.toLinearMap := by
    exact map_smulₛₗ
      (LinearMap.adjoint : (QubitSpace →ₗ[Complex] QubitSpace) ≃ₗ⋆[Complex]
        (QubitSpace →ₗ[Complex] QubitSpace))
      tTwirlAmplitude (tTwirlUnitary i).toLinearEquiv.toLinearMap
  rw [hAdj]
  have hamplitude : (starRingEnd Complex) tTwirlAmplitude * tTwirlAmplitude =
      (3 : Complex)⁻¹ := by
    simpa [one_div] using tTwirlAmplitude_sq
  ext x
  simp [LinearMap.comp_apply, UnitaryTransport.conjOperator,
    (tTwirlUnitary i).adjoint_toLinearMap, mul_comm, mul_assoc]
  rw [← hamplitude]
  ring
end BK05T
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
namespace QEC.Distillation.BK05T
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    tTwirlChannel.mapDensity rho = tTwirl rho := by
  apply densityOperator_ext
  rw [QuantumChannel.mapDensity_toOperator]
  change (tTwirlKraus.toQuantumChannel tTwirlKraus_complete) rho.toOperator =
    (tTwirl rho).toOperator
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp_rw [tTwirlKraus_branch]
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp [DensityOperator.convexCombinationOperator, tTwirlWeight]
end QEC.Distillation.BK05T
