-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterDimension_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:30:13.665204+00:00
-- url     : https://prove2.me/submissions/a520254c-6633-43ea-809c-59da0bff2531

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
private theorem choose_mono_right_le_half {n a b : Nat}
    (hab : a ≤ b) (hb : b ≤ n / 2) :
    Nat.choose n a ≤ Nat.choose n b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hle ih =>
      have hb : b ≤ n / 2 := by omega
      have hlt : b < n / 2 := by omega
      exact (ih hb).trans (Nat.choose_le_succ_of_lt_half_left hlt)
private theorem binomialUpTo_choose_sandwich {n w : Nat}
    (hw : w ≤ n / 2) :
    Nat.choose n w ≤ binomialUpTo n w ∧
      binomialUpTo n w ≤ (w + 1) * Nat.choose n w := by
  unfold binomialUpTo
  constructor
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  · calc
      ∑ i ∈ Finset.Icc 0 w, Nat.choose n i ≤
          ∑ i ∈ Finset.Icc 0 w, Nat.choose n w := by
        apply Finset.sum_le_sum
        intro i hi
        exact choose_mono_right_le_half (Finset.mem_Icc.mp hi).2 hw
      _ = (w + 1) * Nat.choose n w := by simp
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
private theorem binomialUpTo_shifted_choose_sandwich
    (s a : Nat) (hhalf : 2 * a < s) (j : Nat) :
    Nat.choose (s * j + 1) (a * j) ≤ binomialUpTo (s * j + 1) (a * j) ∧
      binomialUpTo (s * j + 1) (a * j) ≤
        (a * j + 1) * Nat.choose (s * j + 1) (a * j) := by
  apply binomialUpTo_choose_sandwich
  by_cases hj : j = 0
  · subst hj
    omega
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hscaled : 2 * (a * j) < s * j := by
      calc
        2 * (a * j) = (2 * a) * j := by ring
        _ < s * j := Nat.mul_lt_mul_of_pos_right hhalf hjpos
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
private theorem tendsto_log_affine_ray_div_zero (a : Nat) :
    Tendsto (fun j : Nat => Real.log (a * j + 1 : ℝ) / j) atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun j : Nat => Real.log (j : ℝ) / j) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hconst_div : Tendsto
      (fun j : Nat => Real.log (a + 1 : ℝ) / j) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat (Real.log (a + 1 : ℝ))
  have hupper : Tendsto
      (fun j : Nat => Real.log ((a + 1) * j : ℝ) / j) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun j : Nat => Real.log (a + 1 : ℝ) / j + Real.log (j : ℝ) / j)
        atTop (𝓝 0) := by
      simpa using hconst_div.add hlog_div
    refine hsum.congr'
      (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
    change _ = Real.log ((a + 1 : ℝ) * (j : ℝ)) / (j : ℝ)
    rw [Real.log_mul (by positivity) (by positivity)]
    field_simp
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (a * j))
    · positivity
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
    have hnat : a * j + 1 ≤ (a + 1) * j := by
      calc
        a * j + 1 ≤ a * j + j := Nat.add_le_add_left hj _
        _ = (a + 1) * j := by ring
    have hlog : Real.log (a * j + 1 : ℝ) ≤ Real.log ((a + 1) * j : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hnat
    exact div_le_div_of_nonneg_right hlog (by positivity)
  · exact hupper
private theorem tendsto_log_dominant_sandwich_div
    (m : Nat) (term total : Nat → Nat) (L : ℝ)
    (hterm : Tendsto
      (fun j : Nat => Real.log (term j : ℝ) / j) atTop (𝓝 L))
    (hterm_pos : ∀ j, 0 < term j)
    (hsand : ∀ j, term j ≤ total j ∧ total j ≤ (m * j + 1) * term j) :
    Tendsto (fun j : Nat => Real.log (total j : ℝ) / j) atTop (𝓝 L) := by
  have hlog_lower : ∀ j, Real.log (term j : ℝ) ≤ Real.log (total j : ℝ) := by
    intro j
    have hterm_posR : (0 : ℝ) < term j := by exact_mod_cast hterm_pos j
    have hterm_le_total : (term j : ℝ) ≤ total j := by exact_mod_cast (hsand j).1
    exact Real.log_le_log hterm_posR hterm_le_total
  have hlog_upper : ∀ j,
      Real.log (total j : ℝ) ≤
        Real.log (term j : ℝ) + Real.log (m * j + 1 : ℝ) := by
    intro j
    have hterm_posR : (0 : ℝ) < term j := by exact_mod_cast hterm_pos j
    have hterm_le_total : (term j : ℝ) ≤ total j := by exact_mod_cast (hsand j).1
    have htotal_posR : (0 : ℝ) < total j := lt_of_lt_of_le hterm_posR hterm_le_total
    have htotal_le : (total j : ℝ) ≤ (m * j + 1 : ℝ) * term j := by
      exact_mod_cast (hsand j).2
    have hfactor_pos : (0 : ℝ) < m * j + 1 := by positivity
    calc
      Real.log (total j : ℝ) ≤ Real.log ((m * j + 1 : ℝ) * term j) :=
        Real.log_le_log htotal_posR htotal_le
      _ = Real.log (term j : ℝ) + Real.log (m * j + 1 : ℝ) := by
        rw [Real.log_mul hfactor_pos.ne' hterm_posR.ne']
        ring
  have hdelta : Tendsto
      (fun j : Nat =>
        (Real.log (total j : ℝ) - Real.log (term j : ℝ)) / j)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
      exact div_nonneg (sub_nonneg.mpr (hlog_lower j)) (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
      have hbound :
          Real.log (total j : ℝ) - Real.log (term j : ℝ) ≤
            Real.log (m * j + 1 : ℝ) := by
        linarith [hlog_upper j]
      exact div_le_div_of_nonneg_right hbound (by positivity)
    · exact tendsto_log_affine_ray_div_zero m
  have hsum : Tendsto
      (fun j : Nat =>
        Real.log (term j : ℝ) / j +
          (Real.log (total j : ℝ) - Real.log (term j : ℝ)) / j)
      atTop (𝓝 L) := by
    simpa using hterm.add hdelta
  refine hsum.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  field_simp
  ring
private theorem tendsto_log_binomialUpTo_shifted_ray_div (s a : Nat)
    (ha : 0 < a) (hhalf : 2 * a < s) (L : ℝ)
    (hchoose : Tendsto
      (fun j : Nat => Real.log (Nat.choose (s * j + 1) (a * j) : ℝ) / j)
      atTop (𝓝 L)) :
    Tendsto
      (fun j : Nat => Real.log (binomialUpTo (s * j + 1) (a * j) : ℝ) / j)
      atTop (𝓝 L) := by
  refine tendsto_log_dominant_sandwich_div a
    (fun j => Nat.choose (s * j + 1) (a * j))
    (fun j => binomialUpTo (s * j + 1) (a * j)) L hchoose ?_ ?_
  · intro j
    have has : a ≤ s := by omega
    exact Nat.choose_pos (Nat.le_trans (Nat.mul_le_mul_right j has) (Nat.le_succ _))
  · intro j
    exact binomialUpTo_shifted_choose_sandwich s a hhalf j
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterDimension A D j : ℝ) / j)
      atTop (𝓝 (parameterDimensionLimit A D)) := by
  have hcomp : 0 < D - A := by omega
  have hhalf : 2 * (6 * A) < 6 * D := by omega
  have hbase := tendsto_log_choose_mul_div (6 * A) (6 * (D - A))
    (by omega) (by omega)
  have hsum : 6 * A + 6 * (D - A) = 6 * D := by omega
  have hsumR : ((6 * A : Nat) : ℝ) + ((6 * (D - A) : Nat) : ℝ) =
      6 * (D : ℝ) := by
    exact_mod_cast hsum
  rw [hsum, hsumR] at hbase
  have hshift := tendsto_log_choose_shifted_ray_div (6 * D) (6 * A)
    (by omega) (by omega)
    (6 * (D : ℝ) * Real.log (6 * D) -
      ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) -
      ((6 * (D - A) : Nat) : ℝ) * Real.log ((6 * (D - A) : Nat) : ℝ)) hbase
  have hprefix := tendsto_log_binomialUpTo_shifted_ray_div (6 * D) (6 * A)
    (by omega) hhalf
    (6 * (D : ℝ) * Real.log (6 * D) -
      ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) -
      ((6 * (D - A) : Nat) : ℝ) * Real.log ((6 * (D - A) : Nat) : ℝ)) hshift
  have hlimit :
      6 * (D : ℝ) * Real.log (6 * D) -
        ((6 * A : Nat) : ℝ) * Real.log ((6 * A : Nat) : ℝ) -
        ((6 * (D - A) : Nat) : ℝ) * Real.log ((6 * (D - A) : Nat) : ℝ) =
          parameterDimensionLimit A D := by
    unfold parameterDimensionLimit entropyRay
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Nat.cast_sub (by omega)]
    ring
  change Tendsto
    (fun j : Nat => Real.log (binomialUpTo (6 * D * j + 1) (6 * A * j) : ℝ) / j)
    atTop (𝓝 (parameterDimensionLimit A D))
  rw [← hlimit]
  exact hprefix
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
