-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:51:54.323004+00:00
-- url     : https://prove2.me/submissions/ccdf5dc3-e921-4810-a30c-9bb0f0738c71

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
section
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace BinaryRowFamily
attribute [-instance] Fintype.ofFinite
private theorem logicalUniformScalar_identity
    (Index : Type u) [Fintype Index] :
    starRingEnd Complex (logicalUniformScalar Index) *
        logicalUniformScalar Index *
        (Nat.card (Qubit.Bitstring Index) : Complex) = 1 := by
  have hcard : 0 < Nat.card (Qubit.Bitstring Index) := Nat.card_pos
  have hsqrtPos :
      0 < Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) *
          (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) =
        (Nat.card (Qubit.Bitstring Index) : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Nat.card (Qubit.Bitstring Index))
  simp only [logicalUniformScalar, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) =
        (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]
private theorem piDivFourPhase_pow_mul_star (n : Nat) :
    piDivFourPhase ^ n * starRingEnd Complex (piDivFourPhase ^ n) = 1 := by
  rw [map_pow, ← mul_pow]
  rw [show piDivFourPhase * starRingEnd Complex piDivFourPhase = 1 by
    simpa [piDivFourPhase] using
      OneQubitMagic.phaseAmplitude_mul_conj (Real.pi / 4)]
  simp
end BinaryRowFamily
end Triorthogonal
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
attribute [-instance] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (Index : Type u) [Fintype Index] [DecidableEq Index] :
    @inner Complex (Qubit.QubitRegister Index)
        (PiLp.innerProductSpace fun _ : Qubit.Bitstring Index => Complex).toInner
        (logicalMagicState Index) (logicalMagicState Index) = 1 := by
  rw [PiLp.inner_apply]
  simp only [logicalMagicState_apply, RCLike.inner_apply, map_mul]
  calc
    ∑ bits, (logicalUniformScalar Index *
          piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits)) *
        (starRingEnd Complex (logicalUniformScalar Index) *
          starRingEnd Complex
            (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits))) =
      ∑ _bits : Qubit.Bitstring Index,
        logicalUniformScalar Index *
          starRingEnd Complex (logicalUniformScalar Index) := by
        apply Finset.sum_congr rfl
        intro bits _hbits
        rw [show
          (logicalUniformScalar Index *
              piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits)) *
            (starRingEnd Complex (logicalUniformScalar Index) *
              starRingEnd Complex
                (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits))) =
            (logicalUniformScalar Index *
              starRingEnd Complex (logicalUniformScalar Index)) *
            (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits) *
              starRingEnd Complex
                (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits))) by ring]
        rw [piDivFourPhase_pow_mul_star]
        simp
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [show Finset.univ.card = Nat.card (Qubit.Bitstring Index) by
        exact Nat.card_eq_fintype_card.symm]
      change (Nat.card (Qubit.Bitstring Index) : Complex) *
          (logicalUniformScalar Index *
            starRingEnd Complex (logicalUniformScalar Index)) = 1
      have h := logicalUniformScalar_identity Index
      calc
        (Nat.card (Qubit.Bitstring Index) : Complex) *
            (logicalUniformScalar Index *
              starRingEnd Complex (logicalUniformScalar Index)) =
          starRingEnd Complex (logicalUniformScalar Index) *
            logicalUniformScalar Index *
              (Nat.card (Qubit.Bitstring Index) : Complex) := by ring
        _ = 1 := h
end QEC.Distillation.Triorthogonal.BinaryRowFamily
