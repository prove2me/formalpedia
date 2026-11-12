-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirl_toOperator_eq_blochProjector_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:30:20.523148+00:00
-- url     : https://prove2.me/submissions/a53c4f68-5e47-4cd7-882d-59c67f5389f0

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliX
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliY
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliZ
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliX
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliY
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliZ
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
private theorem trans_conjOperator
    (U V : UnitaryTransport QubitSpace QubitSpace) (A : Operator QubitSpace) :
    (U.trans V).conjOperator A = V.conjOperator (U.conjOperator A) := by
  ext x
  rfl
private theorem tConjOperator_add
    (U : UnitaryTransport QubitSpace QubitSpace)
    (A B : Operator QubitSpace) :
    U.conjOperator (A + B) = U.conjOperator A + U.conjOperator B := by
  ext psi
  simp [UnitaryTransport.conjOperator]
private theorem tConjOperator_smul
    (U : UnitaryTransport QubitSpace QubitSpace)
    (c : Complex) (A : Operator QubitSpace) :
    U.conjOperator (c • A) = c • U.conjOperator A := by
  ext psi
  simp [UnitaryTransport.conjOperator]
private theorem tHadamard_conj_blochProjector (r : PauliAxis → Real) :
    hadamardTransport.conjOperator (blochProjector r) =
      blochProjector (tHadamardBlochAction r) := by
  simp only [blochProjector, blochOperator, tConjOperator_smul, tConjOperator_add,
    hadamard_conj_one, hadamard_conj_pauliX, hadamard_conj_pauliY,
    hadamard_conj_pauliZ, tHadamardBlochAction]
  module
private theorem tPhase_conj_blochProjector (r : PauliAxis → Real) :
    phaseTransport.conjOperator (blochProjector r) =
      blochProjector (tPhaseBlochAction r) := by
  simp only [blochProjector, blochOperator, tConjOperator_smul, tConjOperator_add,
    phase_conj_one, phase_conj_pauliX, phase_conj_pauliY, phase_conj_pauliZ,
    tPhaseBlochAction]
  module
private theorem tCycle_conj_blochProjector (r : PauliAxis → Real) :
    tCycleTransport.conjOperator (blochProjector r) =
      blochProjector (tCycleBlochAction r) := by
  rw [tCycleTransport, trans_conjOperator, tHadamard_conj_blochProjector,
    tPhase_conj_blochProjector]
  congr 1
  funext i
  fin_cases i <;> simp [tPhaseBlochAction, tHadamardBlochAction,
    tCycleBlochAction]
private theorem tTwirlUnitary_conj_blochProjector
    (i : Fin 3) (r : PauliAxis → Real) :
    (tTwirlUnitary i).conjOperator (blochProjector r) =
      blochProjector ((tCycleBlochAction^[i.1]) r) := by
  fin_cases i
  · rfl
  · exact tCycle_conj_blochProjector r
  · change (tCycleTransport.trans tCycleTransport).conjOperator
      (blochProjector r) = blochProjector
        (tCycleBlochAction (tCycleBlochAction r))
    rw [trans_conjOperator, tCycle_conj_blochProjector,
      tCycle_conj_blochProjector]
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
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    (tTwirl rho).toOperator = blochProjector (tTwirlBloch r) := by
  rw [tTwirl, DensityOperator.convexCombination_toOperator]
  simp only [DensityOperator.convexCombinationOperator,
    UnitaryTransport.conjDensity_toOperator]
  rw [hrho]
  simp_rw [tTwirlUnitary_conj_blochProjector]
  rw [Fin.sum_univ_three]
  simp [tTwirlWeight, blochProjector, blochOperator, tCycleBlochAction,
    tTwirlBloch]
  module
end QEC.Distillation.BK05T
