-- Prove2me | solution 1 for QEC.Distillation.BK05T.tZero_tOne_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:28:50.068883+00:00
-- url     : https://prove2.me/submissions/8c3a0a5d-cb90-4e49-b9e8-f0336686ccb6

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
private theorem tZero_bloch : tBlochOfDirection tZeroDirection = tBloch := by
  funext i
  fin_cases i <;> simp only [tZeroDirection, tReference, tBlochOfDirection, tBloch,
    signedCoordinateValue] <;> norm_num
private theorem tOne_bloch :
    tBlochOfDirection tOneDirection = fun i => -tBloch i := by
  funext i
  fin_cases i <;> simp only [tOneDirection, tBlochOfDirection, tBloch,
    signedCoordinateValue] <;> norm_num
private theorem blochOperator_neg (r : PauliAxis → Real) :
    blochOperator (fun i => -r i) = -blochOperator r := by
  unfold blochOperator
  module
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
theorem _root_.solution : tZero.toOperator * tOne.toOperator = 0 := by
  change blochProjector (tBlochOfDirection tZeroDirection) *
    blochProjector (tBlochOfDirection tOneDirection) = 0
  rw [tZero_bloch, tOne_bloch]
  unfold blochProjector
  rw [blochOperator_neg]
  have hsquare : blochOperator tBloch * blochOperator tBloch = 1 := by
    rw [blochOperator_square, tBloch_normalized]
    norm_num
  rw [smul_mul_smul_comm]
  have hsum : (1 + blochOperator tBloch) * (1 + -blochOperator tBloch) = 0 := by
    simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, hsquare]
    module
  rw [hsum, smul_zero]
end QEC.Distillation.BK05T
