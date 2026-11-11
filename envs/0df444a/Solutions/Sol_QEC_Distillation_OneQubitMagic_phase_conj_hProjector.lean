-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phase_conj_hProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:04:51.871731+00:00
-- url     : https://prove2.me/submissions/54e78c69-54c1-4be3-9d5b-7b7b9e1208cb

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliX
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliY
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliZ
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
private theorem conjOperator_add
    (U : UnitaryTransport QubitSpace QubitSpace)
    (A B : Operator QubitSpace) :
    U.conjOperator (A + B) = U.conjOperator A + U.conjOperator B := by
  ext psi
  simp [UnitaryTransport.conjOperator]
private theorem conjOperator_smul
    (U : UnitaryTransport QubitSpace QubitSpace)
    (c : Complex) (A : Operator QubitSpace) :
    U.conjOperator (c • A) = c • U.conjOperator A := by
  ext psi
  simp [UnitaryTransport.conjOperator]
private theorem phase_conj_blochProjector (r : PauliAxis -> Real) :
    phaseTransport.conjOperator (blochProjector r) =
      blochProjector (phaseBlochAction r) := by
  simp only [blochProjector, blochOperator, conjOperator_smul, conjOperator_add,
    phase_conj_one, phase_conj_pauliX, phase_conj_pauliY,
    phase_conj_pauliZ, phaseBlochAction]
  module
private theorem signedCoordinateValue_neg_smul (c : SignedCoordinate) :
    signedCoordinateValue ((-1 : ℤˣ) • c) = -signedCoordinateValue c := by
  cases c <;> rfl
private theorem phase_hDirection_val (d : HDirection) :
    (phaseClifford • d).1 = phaseClifford.1 • d.1 := rfl
private theorem phase_hBlochOfDirection (d : HDirection) :
    phaseBlochAction (hBlochOfDirection d) =
      hBlochOfDirection (phaseClifford • d) := by
  funext i
  simp only [hBlochOfDirection]
  rw [phase_hDirection_val]
  fin_cases i <;>
    simp [phaseBlochAction, hBlochOfDirection, signedCoordinateValue_neg_smul]
end OneQubitMagic
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (d : HDirection) :
    phaseTransport.conjOperator (hProjector d) =
      hProjector (phaseClifford • d) := by
  simpa only [hProjector, phase_hBlochOfDirection] using
    phase_conj_blochProjector (hBlochOfDirection d)
end QEC.Distillation.OneQubitMagic
