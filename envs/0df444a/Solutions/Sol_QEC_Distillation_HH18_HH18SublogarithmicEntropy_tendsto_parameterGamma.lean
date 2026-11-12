-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_parameterGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:33:29.712693+00:00
-- url     : https://prove2.me/submissions/d5a58723-6836-4b86-938f-5c332bdcb9ed

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_log_parameterLength_div
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_log_parameterDimension_div
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_log_parameterDistance_div
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_parameter_count_ratio_eq_hh18Gamma
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
import Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_choose_succ_le_tail
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
private theorem entropyRay_eq_mul_binEntropy (s a : Nat)
    (ha : 0 < a) (has : a < s) :
    entropyRay s a = (s : ℝ) * Real.binEntropy ((a : ℝ) / s) := by
  have hs : 0 < s := lt_trans ha has
  have hsub : 0 < s - a := Nat.sub_pos_of_lt has
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hsubR : ((s - a : Nat) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hsub
  have hcastSub : ((s - a : Nat) : ℝ) = (s : ℝ) - a := by
    rw [Nat.cast_sub has.le]
  have hone_sub : 1 - (a : ℝ) / s = ((s - a : Nat) : ℝ) / s := by
    rw [hcastSub]
    field_simp [hsR]
  have hinv_a : ((a : ℝ) / s)⁻¹ = (s : ℝ) / a := by
    field_simp [hsR, haR]
  have hinv_sub : (((s - a : Nat) : ℝ) / s)⁻¹ = (s : ℝ) / (s - a) := by
    rw [hcastSub]
    field_simp [hsR, hsubR]
  have hlog_sub : Real.log ((s : ℝ) / ((s : ℝ) - a)) =
      Real.log (s : ℝ) - Real.log ((s - a : Nat) : ℝ) := by
    rw [← hcastSub]
    exact Real.log_div hsR hsubR
  unfold entropyRay Real.binEntropy
  rw [hinv_a, hone_sub, hinv_sub,
    Real.log_div hsR haR, hlog_sub]
  rw [hcastSub]
  field_simp [hsR]
  ring
private theorem parameterDistanceLimit_entropy (A D : Nat)
    (hA : 0 < A) (hwindow : 3 * A < D) :
    parameterDistanceLimit A D =
      (2 * D : ℝ) * Real.binEntropy (3 * (A : ℝ) / D) := by
  have hscaled : 6 * A < 2 * D := by omega
  have hentropy := entropyRay_eq_mul_binEntropy (2 * D) (6 * A)
    (by omega) hscaled
  have hD : (D : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (show 0 < D by omega)
  have hscale : ((6 * A : ℝ) / (2 * D : ℝ)) = 3 * (A : ℝ) / D := by
    push_cast
    field_simp [hD]
    norm_num
  simpa [parameterDistanceLimit, hscale] using hentropy
private theorem parameter_counts_pos (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j ∧
      0 < parameterDimension A D j ∧
      0 < parameterDistance A D j := by
  have hlength_index : parameterW A j < parameterM D j := by
    unfold parameterW parameterM
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j = 2 * (3 * A * j) := by ring
      _ < 2 * (D * j) := htwice
      _ ≤ 6 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 6 * D * j := by ring
      _ < 6 * D * j + 1 := Nat.lt_succ_self _
  have hdistance_index : parameterW A j < parameterR D j + 1 := by
    unfold parameterW parameterR
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j = 2 * (3 * A * j) := by ring
      _ < 2 * (D * j) := htwice
      _ = 2 * D * j := by ring
      _ < 2 * D * j + 1 := Nat.lt_succ_self _
  constructor
  · unfold parameterLength
    exact lt_of_lt_of_le
      (Nat.choose_pos (Nat.succ_le_iff.mpr hlength_index))
      (HH18BinomialTailAsymptotics.choose_succ_le_tail _ _
        (Nat.succ_le_iff.mpr hlength_index))
  constructor
  · unfold parameterDimension binomialUpTo
    calc
      0 < 1 := by omega
      _ = Nat.choose (parameterM D j) 0 := by simp
      _ ≤ ∑ i ∈ Finset.Icc 0 (parameterW A j), Nat.choose (parameterM D j) i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  · unfold parameterDistance
    exact lt_of_lt_of_le
      (Nat.choose_pos (Nat.succ_le_iff.mpr hdistance_index))
      (HH18BinomialTailAsymptotics.choose_succ_le_tail _ _
        (Nat.succ_le_iff.mpr hdistance_index))
private theorem tendsto_parameterGamma_of_log_limits
    {A D : Nat} {LN LK LD : ℝ}
    (hN : Tendsto
      (fun j : Nat => Real.log (parameterLength A D j : ℝ) / j) atTop (𝓝 LN))
    (hK : Tendsto
      (fun j : Nat => Real.log (parameterDimension A D j : ℝ) / j) atTop (𝓝 LK))
    (hD : Tendsto
      (fun j : Nat => Real.log (parameterDistance A D j : ℝ) / j) atTop (𝓝 LD))
    (hLD : LD ≠ 0)
    (hpositive : ∀ᶠ j in atTop,
      0 < parameterLength A D j ∧
        0 < parameterDimension A D j ∧ 0 < parameterDistance A D j) :
    Tendsto (parameterGamma A D) atTop (𝓝 ((LN - LK) / LD)) := by
  have hnumerator : Tendsto
      (fun j : Nat =>
        Real.log (parameterLength A D j : ℝ) / j -
          Real.log (parameterDimension A D j : ℝ) / j)
      atTop (𝓝 (LN - LK)) := hN.sub hK
  have hquotient := hnumerator.div hD hLD
  refine hquotient.congr' ?_
  filter_upwards [hpositive, eventually_ge_atTop (1 : Nat)]
    with j hjpos hj_one
  have hj : 0 < j := Nat.zero_lt_of_lt hj_one
  have hjNat : j ≠ 0 := Nat.ne_of_gt hj
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hjNat
  have hN0 : (parameterLength A D j : ℝ) ≠ 0 := by exact_mod_cast hjpos.1.ne'
  have hK0 : (parameterDimension A D j : ℝ) ≠ 0 := by exact_mod_cast hjpos.2.1.ne'
  unfold parameterGamma
  rw [Real.log_div hN0 hK0]
  rw [Pi.div_apply]
  by_cases hz : Real.log (parameterDistance A D j : ℝ) = 0
  · simp [hz]
  · field_simp [hjR, hz]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindowL : D < 6 * A)
    (hwindowU : 3 * A < D) :
    Tendsto (parameterGamma A D) atTop
      (𝓝 (hh18Gamma ((A : ℝ) / D))) := by
  have hN := tendsto_log_parameterLength_div A D hD hwindowU
  have hK := tendsto_log_parameterDimension_div A D hA hD hwindowU
  have hDistance := tendsto_log_parameterDistance_div A D hA hD
    hwindowL hwindowU
  have hp30 : 0 < 3 * (A : ℝ) / D := by positivity
  have hp31 : 3 * (A : ℝ) / D < 1 := by
    apply (div_lt_one₀ (by positivity : (0 : ℝ) < D)).mpr
    exact_mod_cast hwindowU
  have hLD : parameterDistanceLimit A D ≠ 0 := by
    rw [parameterDistanceLimit_entropy A D hA hwindowU]
    exact mul_ne_zero (by positivity)
      (Real.binEntropy_pos hp30 hp31).ne'
  have hpositive : ∀ᶠ j in atTop,
      0 < parameterLength A D j ∧
        0 < parameterDimension A D j ∧ 0 < parameterDistance A D j := by
    filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj_one
    exact parameter_counts_pos A D j hA hD hwindowU (Nat.zero_lt_of_lt hj_one)
  have hratio := tendsto_parameterGamma_of_log_limits
    hN hK hDistance hLD hpositive
  rw [parameter_count_ratio_eq_hh18Gamma A D hA hD hwindowU] at hratio
  exact hratio
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
