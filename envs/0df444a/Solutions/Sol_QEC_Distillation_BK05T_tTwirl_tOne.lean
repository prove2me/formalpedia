-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirl_tOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:23:15.763195+00:00
-- url     : https://prove2.me/submissions/71f64ca2-b7ea-4ad9-84a7-d4f5e5f2b6f7

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_tMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_tMagicState
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
private theorem trans_conjDensity
    (U V : UnitaryTransport QubitSpace QubitSpace)
    (rho : DensityOperator QubitSpace) :
    (U.trans V).conjDensity rho = V.conjDensity (U.conjDensity rho) := by
  apply densityOperator_ext
  rfl
private theorem tCycle_target_one :
    phaseClifford • (hadamardClifford • tOneDirection) = tOneDirection := by
  decide +kernel
private theorem tCycle_conj_tOne : tCycleTransport.conjDensity tOne = tOne := by
  calc
    tCycleTransport.conjDensity tOne =
        phaseTransport.conjDensity (hadamardTransport.conjDensity tOne) :=
      trans_conjDensity hadamardTransport phaseTransport tOne
    _ = phaseTransport.conjDensity
        (tMagicStateOfDirection (hadamardClifford • tOneDirection)) := by
          change phaseTransport.conjDensity
            (hadamardTransport.conjDensity
              (tMagicStateOfDirection tOneDirection)) = _
          rw [hadamard_conj_tMagicState]
    _ = tMagicStateOfDirection
        (phaseClifford • (hadamardClifford • tOneDirection)) := by
          rw [phase_conj_tMagicState]
    _ = tOne := by
          unfold tOne
          rw [tCycle_target_one]
private theorem tTwirlUnitary_conj_tOne (i : Fin 3) :
    (tTwirlUnitary i).conjDensity tOne = tOne := by
  fin_cases i
  · rfl
  · exact tCycle_conj_tOne
  · change (tCycleTransport.trans tCycleTransport).conjDensity tOne = tOne
    rw [trans_conjDensity, tCycle_conj_tOne, tCycle_conj_tOne]
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
theorem _root_.solution : tTwirl tOne = tOne := by
  apply densityOperator_ext
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp_rw [tTwirlUnitary_conj_tOne]
  simp only [DensityOperator.convexCombinationOperator]
  rw [Fin.sum_univ_three]
  norm_num [tTwirlWeight]
  module
end QEC.Distillation.BK05T
