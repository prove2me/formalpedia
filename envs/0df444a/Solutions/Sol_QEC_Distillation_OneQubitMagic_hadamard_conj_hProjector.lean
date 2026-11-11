-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamard_conj_hProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:04:20.906527+00:00
-- url     : https://prove2.me/submissions/0e0cf034-18c2-4b19-9592-bea0a2d97d11

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliX
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliY
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliZ
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
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
private theorem hadamard_conj_blochProjector (r : PauliAxis -> Real) :
    hadamardTransport.conjOperator (blochProjector r) =
      blochProjector (hadamardBlochAction r) := by
  simp only [blochProjector, blochOperator, conjOperator_smul, conjOperator_add,
    hadamard_conj_one, hadamard_conj_pauliX, hadamard_conj_pauliY,
    hadamard_conj_pauliZ, hadamardBlochAction]
  module
private theorem signedCoordinateValue_neg_smul (c : SignedCoordinate) :
    signedCoordinateValue ((-1 : ℤˣ) • c) = -signedCoordinateValue c := by
  cases c <;> rfl
private theorem hadamard_hDirection_val (d : HDirection) :
    (hadamardClifford • d).1 = hadamardClifford.1 • d.1 := rfl
private theorem hadamard_hBlochOfDirection (d : HDirection) :
    hadamardBlochAction (hBlochOfDirection d) =
      hBlochOfDirection (hadamardClifford • d) := by
  funext i
  simp only [hBlochOfDirection]
  rw [hadamard_hDirection_val]
  fin_cases i <;>
    simp [hadamardBlochAction, hBlochOfDirection, signedCoordinateValue_neg_smul]
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
    hadamardTransport.conjOperator (hProjector d) =
      hProjector (hadamardClifford • d) := by
  simpa only [hProjector, hadamard_hBlochOfDirection] using
    hadamard_conj_blochProjector (hBlochOfDirection d)
end QEC.Distillation.OneQubitMagic
