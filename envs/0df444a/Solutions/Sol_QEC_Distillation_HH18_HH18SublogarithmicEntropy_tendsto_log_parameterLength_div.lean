-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterLength_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:30:10.455528+00:00
-- url     : https://prove2.me/submissions/86e46b46-bf07-4f0a-b47e-eea18e122763

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
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
import Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_binomialTail_le_two_pow
import Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_tendsto_log_factorial_mul_div_sub
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
private theorem choose_shifted_ray_le_two_choose_ray (s a : Nat)
    (ha : 0 < a) (hhalf : 2 * a ≤ s) (j : Nat) (hj : 0 < j) :
    Nat.choose (s * j + 1) (a * j) ≤ 2 * Nat.choose (s * j) (a * j) := by
  have hak : 0 < a * j := Nat.mul_pos ha hj
  have hhalf_index : a * j - 1 < (s * j) / 2 := by
    have hscaled : 2 * (a * j) ≤ s * j := by
      calc
        2 * (a * j) = (2 * a) * j := by ring
        _ ≤ s * j := Nat.mul_le_mul_right j hhalf
    omega
  have hprev := Nat.choose_le_succ_of_lt_half_left hhalf_index
  have hprev' :
      Nat.choose (s * j) (a * j - 1) ≤ Nat.choose (s * j) (a * j) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hak)] using hprev
  rw [Nat.choose_succ_left (s * j) (a * j) hak]
  omega
private theorem tendsto_log_choose_mul_div (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun j : Nat => Real.log (Nat.choose ((a + b) * j) (a * j) : ℝ) / j)
      atTop
      (𝓝 ((a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b)) := by
  have hab : 0 < a + b := Nat.add_pos_left ha _
  have hN := HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub
    (a + b) hab
  have hA := HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub a ha
  have hB := HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub b hb
  have hrays : Tendsto
      (fun j : Nat =>
        (Real.log (((a + b) * j).factorial : ℝ) / j - (a + b) * Real.log j) -
          (Real.log ((a * j).factorial : ℝ) / j - a * Real.log j) -
          (Real.log ((b * j).factorial : ℝ) / j - b * Real.log j))
      atTop
      (𝓝 ((a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b)) := by
    convert (hN.sub hA).sub hB using 1
    · ext j
      push_cast
      ring
    · congr 1
      push_cast
      ring
  refine hrays.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hk : a * j ≤ (a + b) * j :=
    Nat.mul_le_mul_right j (Nat.le_add_right a b)
  have hsub : (a + b) * j - a * j = b * j := by
    rw [Nat.add_mul, Nat.add_sub_cancel_left]
  have hchoose_pos : (0 : ℝ) < Nat.choose ((a + b) * j) (a * j) := by
    exact_mod_cast Nat.choose_pos hk
  have hfactA_pos : (0 : ℝ) < (a * j).factorial := by positivity
  have hfactB_pos : (0 : ℝ) < (b * j).factorial := by positivity
  have hfactorial :
      (Nat.choose ((a + b) * j) (a * j) : ℝ) * (a * j).factorial *
          (b * j).factorial = ((a + b) * j).factorial := by
    have hfactorial_nat := Nat.choose_mul_factorial_mul_factorial hk
    rw [hsub] at hfactorial_nat
    exact_mod_cast hfactorial_nat
  have hlog_choose :
      Real.log (Nat.choose ((a + b) * j) (a * j) : ℝ) =
        Real.log (((a + b) * j).factorial : ℝ) -
          Real.log ((a * j).factorial : ℝ) -
          Real.log ((b * j).factorial : ℝ) := by
    rw [← hfactorial,
      Real.log_mul (mul_ne_zero hchoose_pos.ne' hfactA_pos.ne')
        hfactB_pos.ne',
      Real.log_mul hchoose_pos.ne' hfactA_pos.ne']
    ring
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  change _ = Real.log (Nat.choose ((a + b) * j) (a * j) : ℝ) / (j : ℝ)
  rw [hlog_choose]
  field_simp [hjR]
  ring
private theorem tendsto_log_choose_shifted_ray_div (s a : Nat)
    (ha : 0 < a) (hhalf : 2 * a ≤ s) (L : ℝ)
    (hbase : Tendsto
      (fun j : Nat => Real.log (Nat.choose (s * j) (a * j) : ℝ) / j)
      atTop (𝓝 L)) :
    Tendsto
      (fun j : Nat => Real.log (Nat.choose (s * j + 1) (a * j) : ℝ) / j)
      atTop (𝓝 L) := by
  let base : Nat → ℝ := fun j => Nat.choose (s * j) (a * j)
  let shifted : Nat → ℝ := fun j => Nat.choose (s * j + 1) (a * j)
  have hlog_two_div : Tendsto (fun j : Nat => Real.log 2 / j) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hdelta : Tendsto
      (fun j : Nat => (Real.log (shifted j) - Real.log (base j)) / j)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · apply Filter.Eventually.of_forall
      intro j
      have has : a ≤ s := by omega
      have hbase_pos : 0 < base j := by
        dsimp [base]
        exact_mod_cast Nat.choose_pos (Nat.mul_le_mul_right j has)
      have hmono : base j ≤ shifted j := by
        dsimp [base, shifted]
        exact_mod_cast (by
          simpa [Nat.succ_eq_add_one] using Nat.choose_le_succ (s * j) (a * j))
      exact div_nonneg (sub_nonneg.mpr (Real.log_le_log hbase_pos hmono))
        (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
      have has : a ≤ s := by omega
      have hbase_pos : 0 < base j := by
        dsimp [base]
        exact_mod_cast Nat.choose_pos (Nat.mul_le_mul_right j has)
      have hshift_pos : 0 < shifted j := by
        dsimp [shifted]
        exact_mod_cast Nat.choose_pos
          (Nat.le_trans (Nat.mul_le_mul_right j has) (Nat.le_succ _))
      have hfactor : shifted j ≤ 2 * base j := by
        dsimp [base, shifted]
        exact_mod_cast choose_shifted_ray_le_two_choose_ray s a ha hhalf j
          (Nat.zero_lt_of_lt hj)
      have hlog_factor : Real.log (shifted j) ≤ Real.log (2 * base j) := by
        exact Real.log_le_log hshift_pos hfactor
      have hlog_upper : Real.log (shifted j) - Real.log (base j) ≤ Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbase_pos.ne'] at hlog_factor
        linarith
      exact div_le_div_of_nonneg_right hlog_upper (by positivity)
    · exact hlog_two_div
  have hsum : Tendsto
      (fun j : Nat =>
        Real.log (base j) / j + (Real.log (shifted j) - Real.log (base j)) / j)
      atTop (𝓝 L) := by
    simpa using hbase.add hdelta
  refine hsum.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  dsimp [base, shifted] at *
  field_simp
  ring
private theorem central_choose_le_parameterLength (A D j : Nat)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    Nat.choose (6 * D * j + 1) (3 * D * j) ≤ parameterLength A D j := by
  unfold parameterLength parameterM parameterW
  unfold binomialTail
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  simp only [Finset.mem_Icc]
  have hcenter : 6 * A * j + 1 ≤ 3 * D * j := by
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j + 1 = 2 * (3 * A * j) + 1 := by ring
      _ ≤ 2 * (D * j) := Nat.succ_le_iff.mpr htwice
      _ ≤ 3 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 3 * D * j := by ring
  constructor
  · exact hcenter
  · calc
      3 * D * j = 3 * (D * j) := by ring
      _ ≤ 6 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 6 * D * j := by ring
      _ ≤ 6 * D * j + 1 := Nat.le_succ _
private theorem tendsto_log_two_pow_shifted_ray_div (D : Nat) :
    Tendsto
      (fun j : Nat => Real.log ((2 ^ (6 * D * j + 1) : Nat) : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
  have hzero : Tendsto (fun j : Nat => Real.log 2 / j) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hmain : Tendsto
      (fun j : Nat => 6 * (D : ℝ) * Real.log 2 + Real.log 2 / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
    simpa [parameterLengthLimit] using
      (tendsto_const_nhds (x := 6 * (D : ℝ) * Real.log 2)).add hzero
  refine hmain.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  push_cast
  rw [Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterLength A D j : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
  have hcentral_base : Tendsto
      (fun j : Nat =>
        Real.log (Nat.choose ((3 * D + 3 * D) * j) (3 * D * j) : ℝ) / j)
      atTop
      (𝓝 ((((3 * D : Nat) : ℝ) + ((3 * D : Nat) : ℝ)) *
          Real.log (((3 * D : Nat) : ℝ) + ((3 * D : Nat) : ℝ)) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ))) :=
    tendsto_log_choose_mul_div (3 * D) (3 * D) (by omega) (by omega)
  have hcentral_base' : Tendsto
      (fun j : Nat => Real.log (Nat.choose (6 * D * j) (3 * D * j) : ℝ) / j)
      atTop
      (𝓝 (6 * D * Real.log (6 * D) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ))) := by
    have hsum : 3 * D + 3 * D = 6 * D := by omega
    have hsumR : ((3 * D : Nat) : ℝ) + ((3 * D : Nat) : ℝ) = 6 * (D : ℝ) := by
      exact_mod_cast hsum
    rw [hsum] at hcentral_base
    simpa only [hsumR] using hcentral_base
  have hcentral : Tendsto
      (fun j : Nat => Real.log (Nat.choose (6 * D * j + 1) (3 * D * j) : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by
    have hshift := tendsto_log_choose_shifted_ray_div (6 * D) (3 * D)
      (by omega) (by omega)
      (6 * D * Real.log (6 * D) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
        ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ)) hcentral_base'
    have hlog : Real.log (6 * (D : ℝ)) = Real.log 2 + Real.log (3 * D) := by
      rw [show 6 * (D : ℝ) = 2 * (3 * D) by ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hlimit :
        6 * (D : ℝ) * Real.log (6 * D) -
          ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) -
          ((3 * D : Nat) : ℝ) * Real.log ((3 * D : Nat) : ℝ) =
            parameterLengthLimit D := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      unfold parameterLengthLimit
      rw [hlog]
      ring
    rw [← hlimit]
    exact hshift
  have hupper := tendsto_log_two_pow_shifted_ray_div D
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hcentral hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj_one
    have hj : 0 < j := Nat.zero_lt_of_lt hj_one
    have hterm_pos : (0 : ℝ) < Nat.choose (6 * D * j + 1) (3 * D * j) := by
      have hindex : 3 * D * j ≤ 6 * D * j + 1 := by
        have hscale : 3 * (D * j) ≤ 6 * (D * j) :=
          Nat.mul_le_mul_right (D * j) (by omega)
        calc
          3 * D * j = 3 * (D * j) := by ring
          _ ≤ 6 * (D * j) := hscale
          _ = 6 * D * j := by ring
          _ ≤ 6 * D * j + 1 := Nat.le_succ _
      exact_mod_cast Nat.choose_pos hindex
    have hterm_le :
        (Nat.choose (6 * D * j + 1) (3 * D * j) : ℝ) ≤ parameterLength A D j := by
      exact_mod_cast central_choose_le_parameterLength A D j hwindow hj
    exact div_le_div_of_nonneg_right (Real.log_le_log hterm_pos hterm_le)
      (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj_one
    have hj : 0 < j := Nat.zero_lt_of_lt hj_one
    have htail_le : parameterLength A D j ≤ 2 ^ (6 * D * j + 1) := by
      exact
        HH18BinomialTailAsymptotics.binomialTail_le_two_pow
          (6 * D * j + 1) (6 * A * j)
    have htail_pos : (0 : ℝ) < parameterLength A D j := by
      have hindex : 3 * D * j ≤ 6 * D * j + 1 := by
        have hscale : 3 * (D * j) ≤ 6 * (D * j) :=
          Nat.mul_le_mul_right (D * j) (by omega)
        calc
          3 * D * j = 3 * (D * j) := by ring
          _ ≤ 6 * (D * j) := hscale
          _ = 6 * D * j := by ring
          _ ≤ 6 * D * j + 1 := Nat.le_succ _
      have hterm_pos : 0 < Nat.choose (6 * D * j + 1) (3 * D * j) :=
        Nat.choose_pos hindex
      have htail_posNat : 0 < parameterLength A D j := lt_of_lt_of_le hterm_pos
        (central_choose_le_parameterLength A D j hwindow hj)
      exact_mod_cast htail_posNat
    have htail_leR : (parameterLength A D j : ℝ) ≤
        ((2 ^ (6 * D * j + 1) : Nat) : ℝ) := by
      exact_mod_cast htail_le
    exact div_le_div_of_nonneg_right (Real.log_le_log htail_pos htail_leR)
      (by positivity)
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
