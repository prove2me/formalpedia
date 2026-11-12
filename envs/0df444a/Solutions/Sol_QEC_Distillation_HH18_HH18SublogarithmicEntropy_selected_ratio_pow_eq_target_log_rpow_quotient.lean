-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_eq_target_log_rpow_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:14:46.523195+00:00
-- url     : https://prove2.me/submissions/77e2348f-f3c4-4cbf-8f72-8e377bd2c5be

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_counts_nontrivial
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
private theorem log_inv_doublePowerTarget {q : ℝ} {d z : Nat}
    (_hq0 : 0 < q) :
    Real.log (1 / doublePowerTarget q d z) =
      (d : ℝ) ^ z * Real.log (1 / q) := by
  unfold doublePowerTarget
  rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
  push_cast
  ring
private theorem ratio_pow_eq_rpow_depth_base {n k d z : Nat}
    (hn : 0 < n) (hk : 0 < k) (hd : 1 < d) :
    ((n : ℝ) / k) ^ z =
      Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) := by
  have hratio : 0 < (n : ℝ) / k := by
    exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hk)
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hdPos : 0 < (d : ℝ) := lt_trans zero_lt_one hdReal
  have hbase : 0 < (d : ℝ) ^ z := pow_pos hdPos _
  have hlogd : 0 < Real.log d := Real.log_pos hdReal
  calc
    ((n : ℝ) / k) ^ z = Real.rpow ((n : ℝ) / k) (z : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.exp (Real.log ((n : ℝ) / k) * (z : ℝ)) :=
      Real.rpow_def_of_pos hratio _
    _ = Real.exp
        (Real.log ((d : ℝ) ^ z) * concatenationExponent n k d) := by
      congr 1
      rw [Real.log_pow]
      unfold concatenationExponent
      field_simp [ne_of_gt hlogd]
    _ = Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) :=
      (Real.rpow_def_of_pos hbase _).symm
private theorem ratio_pow_eq_target_log_rpow_quotient {q : ℝ} {n k d z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hn : 0 < n) (hk : 0 < k) (hd : 1 < d) :
    ((n : ℝ) / k) ^ z =
      Real.rpow (Real.log (1 / doublePowerTarget q d z))
          (concatenationExponent n k d) /
        Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hone_div : 1 < (1 / q) := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  have hlogq : 0 < Real.log (1 / q) := Real.log_pos hone_div
  have hrpowq : 0 < Real.rpow (Real.log (1 / q))
      (concatenationExponent n k d) :=
    Real.rpow_pos_of_pos hlogq _
  have hmul :
      Real.rpow ((d : ℝ) ^ z * Real.log (1 / q))
          (concatenationExponent n k d) =
        Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) *
          Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
    simpa only [Real.rpow_eq_pow] using
      (Real.mul_rpow (by positivity : 0 ≤ (d : ℝ) ^ z) hlogq.le
        (z := concatenationExponent n k d))
  rw [ratio_pow_eq_rpow_depth_base hn hk hd]
  rw [log_inv_doublePowerTarget hq0]
  calc
    Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) =
        (Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) *
          Real.rpow (Real.log (1 / q)) (concatenationExponent n k d)) /
          Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
      field_simp [ne_of_gt hrpowq]
    _ = Real.rpow ((d : ℝ) ^ z * Real.log (1 / q))
          (concatenationExponent n k d) /
        Real.rpow (Real.log (1 / q)) (concatenationExponent n k d) := by
      exact congrArg
        (fun x : ℝ => x / Real.rpow (Real.log (1 / q)) (concatenationExponent n k d))
        hmul.symm
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution
    {q : ℝ} {A D j z : Nat} (hq0 : 0 < q) (hq1 : q < 1)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z =
      Real.rpow (Real.log (1 / selectedDoublePowerTarget q A D j z))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) /
        Real.rpow (Real.log (1 / q))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) := by
  rcases selected_parameter_counts_nontrivial A D j hD hwindow hj with
    ⟨hn, hk, hd⟩
  simpa [selectedDoublePowerTarget] using
    ratio_pow_eq_target_log_rpow_quotient (q := q)
      (n := parameterLength A D j) (k := parameterDimension A D j)
      (d := parameterDistance A D j) (z := z) hq0 hq1 hn hk hd
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
