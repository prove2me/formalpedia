-- Prove2me | solution 1 for QEC.Distillation.BK05T.tInputSquaredOverlap_eq_bloch_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:30:24.334758+00:00
-- url     : https://prove2.me/submissions/677cbe26-4133-4255-aaba-149993b17693

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
import Theorems.Thm_QEC_Distillation_OneQubitMagic_trace_pauli_mul_blochProjector
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_trace
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
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    tInputSquaredOverlap rho =
      (1 + (r .x + r .y + r .z) / Real.sqrt 3) / 2 := by
  unfold tInputSquaredOverlap projectionSquaredOverlap
  rw [hrho]
  have hprojector : tProjector tZeroDirection =
      (2 : Complex)⁻¹ • (1 + (Real.sqrt 3 : Complex)⁻¹ •
        (pauliX + pauliY + pauliZ)) := by
    simp [tProjector, tZeroDirection, tReference, tBlochOfDirection,
      signedCoordinateValue, blochProjector, blochOperator]
  have htrace : LinearMap.trace Complex QubitSpace (blochProjector r) = 1 := by
    simp [blochProjector, blochOperator, pauliX_trace, pauliY_trace,
      pauliZ_trace]
  have htx : LinearMap.trace Complex QubitSpace (pauliX * blochProjector r) = r .x := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .x
  have hty : LinearMap.trace Complex QubitSpace (pauliY * blochProjector r) = r .y := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .y
  have htz : LinearMap.trace Complex QubitSpace (pauliZ * blochProjector r) = r .z := by
    simpa [pauliOperator] using trace_pauli_mul_blochProjector r .z
  rw [hprojector]
  simp only [smul_mul_assoc, add_mul, one_mul, map_smul, map_add, htrace]
  rw [htx, hty, htz]
  have hsqrt : Real.sqrt (3 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtSq : Real.sqrt (3 : Real) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  norm_num
  field_simp [hsqrt]
  ring_nf
  rw [hsqrtSq]
  ring
end QEC.Distillation.BK05T
