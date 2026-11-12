-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirl_diagonalInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:23:49.126015+00:00
-- url     : https://prove2.me/submissions/f760b752-b48a-4b87-83fb-5d988f785cb1

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_toOperator
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
private theorem tCycle_target_zero :
    phaseClifford • (hadamardClifford • tZeroDirection) = tZeroDirection := by
  decide +kernel
private theorem tCycle_target_one :
    phaseClifford • (hadamardClifford • tOneDirection) = tOneDirection := by
  decide +kernel
private theorem tCycle_conj_tZero : tCycleTransport.conjDensity tZero = tZero := by
  calc
    tCycleTransport.conjDensity tZero =
        phaseTransport.conjDensity (hadamardTransport.conjDensity tZero) :=
      trans_conjDensity hadamardTransport phaseTransport tZero
    _ = phaseTransport.conjDensity
        (tMagicStateOfDirection (hadamardClifford • tZeroDirection)) := by
          change phaseTransport.conjDensity
            (hadamardTransport.conjDensity
              (tMagicStateOfDirection tZeroDirection)) = _
          rw [hadamard_conj_tMagicState]
    _ = tMagicStateOfDirection
        (phaseClifford • (hadamardClifford • tZeroDirection)) := by
          rw [phase_conj_tMagicState]
    _ = tZero := by
          unfold tZero
          rw [tCycle_target_zero]
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
private theorem tTwirlUnitary_conj_tZero (i : Fin 3) :
    (tTwirlUnitary i).conjDensity tZero = tZero := by
  fin_cases i
  · rfl
  · exact tCycle_conj_tZero
  · change (tCycleTransport.trans tCycleTransport).conjDensity tZero = tZero
    rw [trans_conjDensity, tCycle_conj_tZero, tCycle_conj_tZero]
private theorem tTwirlUnitary_conj_tOne (i : Fin 3) :
    (tTwirlUnitary i).conjDensity tOne = tOne := by
  fin_cases i
  · rfl
  · exact tCycle_conj_tOne
  · change (tCycleTransport.trans tCycleTransport).conjDensity tOne = tOne
    rw [trans_conjDensity, tCycle_conj_tOne, tCycle_conj_tOne]
private theorem tTwirlUnitary_conj_tInputComponent
    (i : Fin 3) (word : Fin 2) :
    (tTwirlUnitary i).conjDensity (tInputComponent word) = tInputComponent word := by
  fin_cases word
  · exact tTwirlUnitary_conj_tZero i
  · exact tTwirlUnitary_conj_tOne i
private theorem tTwirlUnitary_conj_tRawInputBranch
    (epsilon : Real) (i : Fin 3) (word : Fin 2) :
    (tTwirlUnitary i).conjOperator (tRawInputBranch epsilon word) =
      tRawInputBranch epsilon word := by
  unfold tRawInputBranch
  change (tTwirlUnitary i).conjOperatorLinearMap
    ((tInputWeight epsilon word : Complex) • (tInputComponent word).toOperator) = _
  rw [map_smul]
  exact congrArg (fun sigma : DensityOperator QubitSpace =>
    (tInputWeight epsilon word : Complex) • sigma.toOperator)
    (tTwirlUnitary_conj_tInputComponent i word)
private theorem tTwirlUnitary_conj_tDiagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (i : Fin 3) :
    (tTwirlUnitary i).conjDensity (tDiagonalInput epsilon hzero hone) =
      tDiagonalInput epsilon hzero hone := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator, tDiagonalInput_toOperator]
  change (tTwirlUnitary i).conjOperatorLinearMap
    (∑ word : Fin 2, tRawInputBranch epsilon word) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _hword
  exact tTwirlUnitary_conj_tRawInputBranch epsilon i word
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
theorem _root_.solution
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tTwirl (tDiagonalInput epsilon hzero hone) = tDiagonalInput epsilon hzero hone := by
  apply densityOperator_ext
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp_rw [tTwirlUnitary_conj_tDiagonalInput epsilon hzero hone]
  simp only [DensityOperator.convexCombinationOperator]
  rw [Fin.sum_univ_three]
  norm_num [tTwirlWeight]
  module
end QEC.Distillation.BK05T
