-- Prove2me | solution 1 for QEC.Coding.why24U_fieldClifford_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:34:14.567999+00:00
-- url     : https://prove2.me/submissions/cfc31cfc-792b-455c-b38a-416e58e6f814

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_adjoint
import Theorems.Thm_QEC_Coding_why24U_isUnitary
import Theorems.Thm_QEC_Coding_why24U_conjX_three
import Theorems.Thm_QEC_Coding_why24QuditZ_mul
import Theorems.Thm_QEC_Coding_why24U_mul_qZ
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
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
attribute [local simp] QEC.Coding.why24QuditZ_apply
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


attribute [local simp] QEC.Coding.why24U_apply
section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
private theorem why24PauliPhase_add_two_mul (a : ZMod 4) (t : ZMod 2) :
    why24PauliPhase (a + 2 * (t.val : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar t := by
  fin_cases t
  · change why24PauliPhase (a + 2 * (0 : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar 0
    simp [why24PauliPhase]
  · change why24PauliPhase (a + 2 * (1 : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar 1
    rw [PauliSymplectic.binaryPhaseScalar_one]
    fin_cases a
    · change Complex.I ^ 2 = Complex.I ^ 0 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 3 = Complex.I ^ 1 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 0 = Complex.I ^ 2 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 1 = Complex.I ^ 3 * (-1)
      norm_num [pow_succ, Complex.I_sq]
private theorem why24U_conjPauli_three (β : F1024) (a : ZMod 4)
    (b c : F1024) :
    why24U β 3 * why24FieldPauliOperator (a, b, c) * LinearMap.adjoint (why24U β 3) =
      why24FieldPauliOperator
        (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 3)).val : ZMod 4), b,
          why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c) := by
  change why24U β 3 *
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        LinearMap.adjoint (why24U β 3) = _
  rw [show why24U β 3 * (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
      LinearMap.adjoint (why24U β 3) = why24PauliPhase a •
        (why24U β 3 * why24QuditX b * why24QuditZ c *
          LinearMap.adjoint (why24U β 3)) by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]]
  have hcomm := why24U_mul_qZ β 3 c
  have hcommAdj : why24QuditZ c * LinearMap.adjoint (why24U β 3) =
      LinearMap.adjoint (why24U β 3) * why24QuditZ c := by
    rw [why24U_adjoint]
    exact hcomm.symm
  rw [show why24U β 3 * why24QuditX b * why24QuditZ c *
      LinearMap.adjoint (why24U β 3) =
      (why24U β 3 * why24QuditX b * LinearMap.adjoint (why24U β 3)) *
        why24QuditZ c by
        calc
          why24U β 3 * why24QuditX b * why24QuditZ c *
              LinearMap.adjoint (why24U β 3) =
              (why24U β 3 * why24QuditX b) *
                (why24QuditZ c * LinearMap.adjoint (why24U β 3)) := by
                rw [mul_assoc]
          _ = (why24U β 3 * why24QuditX b) *
              (LinearMap.adjoint (why24U β 3) * why24QuditZ c) := by
                rw [hcommAdj]
          _ = (why24U β 3 * why24QuditX b * LinearMap.adjoint (why24U β 3)) *
              why24QuditZ c := by
                simp only [mul_assoc]]
  rw [why24U_conjX_three]
  rw [smul_mul_assoc]
  rw [show (why24QuditX b *
      why24QuditZ (why24FrobeniusRootTwo (β * b) + β * b ^ 2)) * why24QuditZ c =
      why24QuditX b *
        why24QuditZ (why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c) by
      rw [mul_assoc, why24QuditZ_mul]]
  change why24PauliPhase a •
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * b ^ 3)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c))) =
    why24PauliPhase
      (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 3)).val : ZMod 4)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c))
  rw [why24PauliPhase_add_two_mul, mul_smul]
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β : F1024) : Why24FieldClifford (why24U β 3) := by
  constructor
  · exact why24U_isUnitary β 3
  · rintro ⟨a, b, c⟩
    refine ⟨(a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 3)).val : ZMod 4), b,
      why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c), ?_⟩
    exact why24U_conjPauli_three β a b c
end QEC.Coding
