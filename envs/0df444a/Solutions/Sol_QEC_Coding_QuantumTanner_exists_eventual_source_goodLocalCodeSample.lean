-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_source_goodLocalCodeSample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:09:13.917955+00:00
-- url     : https://prove2.me/submissions/d31bc600-3f5c-472f-96bb-1b51edcd2c1d

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_cast_le
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_add_one
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_degree
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_iff_exists
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_of_union_bound
import Theorems.Thm_QEC_Coding_QuantumTanner_card_binaryLowWeightWords
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_rowCombination_lowWeight_of_not_codeA_distance
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_rankFailureWitness_of_not_fullRowRank
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_lowWeight_kernel_of_not_codeB_distance
import Theorems.Thm_QEC_Coding_QuantumTanner_goodLocalCodeEvent_of_fullRowRank
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_BPTMeasurementDistance_mono
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
section RobustnessAsymptotics
open Filter
private theorem exists_eventual_puncture_floor_linear_margin
    (gamma delta : ℝ) (hGamma : gamma < 1) (hDelta : 0 < delta) :
    ∃ threshold : Nat, ∀ degree : Nat, threshold ≤ degree →
      2 ≤ degree ∧
        (Nat.floor ((degree : ℝ) ^ gamma) : ℝ) < delta / 4 * degree := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hGamma)).eventually
    (gt_mem_nhds (show (0 : ℝ) < delta / 4 by positivity))
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨threshold, hThreshold⟩ := eventually_atTop.mp hNat
  refine ⟨max threshold 2, ?_⟩
  intro degree hDegree
  have hTwo : 2 ≤ degree := (Nat.le_max_right _ _).trans hDegree
  have hPos : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have hPower : (degree : ℝ) ^ gamma =
      (degree : ℝ) ^ (-(1 - gamma)) * degree := by
    calc
      (degree : ℝ) ^ gamma = (degree : ℝ) ^ (-(1 - gamma) + 1) := by
        congr 1
        ring
      _ = (degree : ℝ) ^ (-(1 - gamma)) * (degree : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add hPos _ _
      _ = (degree : ℝ) ^ (-(1 - gamma)) * degree := by rw [Real.rpow_one]
  refine ⟨hTwo, ?_⟩
  calc
    (Nat.floor ((degree : ℝ) ^ gamma) : ℝ) ≤ (degree : ℝ) ^ gamma :=
      Nat.floor_le (Real.rpow_nonneg hPos.le _)
    _ = (degree : ℝ) ^ (-(1 - gamma)) * degree := hPower
    _ < delta / 4 * degree :=
      mul_lt_mul_of_pos_right
        (hThreshold degree ((Nat.le_max_left _ _).trans hDegree)) hPos
end RobustnessAsymptotics
section RobustnessIndexBounds
private theorem partialChooseSum_le (n k : Nat) :
    (∑ i ∈ Finset.range (k + 1), Nat.choose n i) ≤ (k + 1) * (n + 1) ^ k := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (n + 1) ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact (Nat.choose_le_pow n i).trans
        ((pow_le_pow_left' (Nat.le_succ n) i).trans
          (pow_le_pow_right' (by omega : 1 ≤ n + 1) hik))
    _ = _ := by simp
private theorem matchingChooseSum_le (n q : Nat) :
    (∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) ≤
      (q + 1) * (n + 1) ^ (2 * q) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (q + 1), (n + 1) ^ (2 * q) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hc : Nat.choose n i ≤ (n + 1) ^ q :=
        (Nat.choose_le_pow n i).trans
          ((pow_le_pow_left' (Nat.le_succ n) i).trans
            (pow_le_pow_right' (by omega : 1 ≤ n + 1) hiq))
      simpa only [← pow_add, two_mul] using Nat.mul_le_mul hc hc
    _ = _ := by simp
private theorem robustIndexNumerator_le (n q cutoff : Nat)
    (hq : q ≤ n) (hc : cutoff ≤ n) :
    2 * ((∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) *
      (2 ^ n * (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ^ n)) ≤
        2 ^ (n + 1) * (n + 1) ^ (2 * q + 1 + (cutoff + 1) * n) := by
  have hMatch : (∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) ≤
      (n + 1) ^ (2 * q + 1) := by
    calc
      _ ≤ (q + 1) * (n + 1) ^ (2 * q) := matchingChooseSum_le n q
      _ ≤ (n + 1) * (n + 1) ^ (2 * q) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hBall : (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ≤
      (n + 1) ^ (cutoff + 1) := by
    calc
      _ ≤ (cutoff + 1) * (n + 1) ^ cutoff := partialChooseSum_le n cutoff
      _ ≤ (n + 1) * (n + 1) ^ cutoff := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ 2 * ((n + 1) ^ (2 * q + 1) *
        (2 ^ n * ((n + 1) ^ (cutoff + 1)) ^ n)) := by
      gcongr
    _ = _ := by simp only [pow_mul, pow_add, pow_succ]; ring
private theorem robustIndexNumerator_le_pow (n q cutoff t : Nat)
    (hq : q ≤ n) (hc : cutoff ≤ n) (ht : n + 1 ≤ 2 ^ t) :
    2 * ((∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) *
      (2 ^ n * (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ^ n)) ≤
      2 ^ (n + 1 + t * (2 * q + 1 + (cutoff + 1) * n)) := by
  calc
    _ ≤ 2 ^ (n + 1) * (n + 1) ^ (2 * q + 1 + (cutoff + 1) * n) :=
      robustIndexNumerator_le n q cutoff hq hc
    _ ≤ 2 ^ (n + 1) * (2 ^ t) ^ (2 * q + 1 + (cutoff + 1) * n) :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' ht _)
    _ = _ := by rw [← pow_mul, ← pow_add]
private theorem robustIndexNumerator_le_pow_clog (n q cutoff : Nat)
    (hq : q ≤ n) (hc : cutoff ≤ n) :
    2 * ((∑ i ∈ Finset.range (q + 1), Nat.choose n i * Nat.choose n i) *
      (2 ^ n * (∑ i ∈ Finset.range (cutoff + 1), Nat.choose n i) ^ n)) ≤
      2 ^ (n + 1 + Nat.clog 2 (n + 1) * (2 * q + 1 + (cutoff + 1) * n)) := by
  exact robustIndexNumerator_le_pow n q cutoff (Nat.clog 2 (n + 1)) hq hc
    (Nat.le_pow_clog (by decide) (n + 1))
private theorem binaryCeilLog_lt_logb_add_two {n : Nat} (hn : 1 ≤ n) :
    (Nat.clog 2 (n + 1) : ℝ) < Real.logb 2 (n : ℝ) + 2 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hCeil : (Nat.clog 2 (n + 1) : ℝ) < Real.logb 2 (n + 1 : Nat) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (Real.logb_nonneg hb (by exact_mod_cast (by omega : 1 ≤ n + 1)))
  have hLog : Real.logb 2 (n + 1 : Nat) ≤ Real.logb 2 (2 * (n : ℝ)) := by
    apply Real.logb_le_logb_of_le hb
    · positivity
    · push_cast
      have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hProduct : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnReal)]
    norm_num [Real.logb]
  linarith
open Filter
private theorem exists_eventual_rpow_logb_margin
    (a s c : ℝ) (hGap : a < s) (hc : 0 < c) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ (n : ℝ) ^ a * Real.logb 2 n < c * (n : ℝ) ^ s := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hSmall := (isLittleO_log_rpow_atTop (sub_pos.mpr hGap)).bound
    (show 0 < c * Real.log 2 / 2 by positivity)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨threshold, hThreshold⟩ := eventually_atTop.mp hNat
  refine ⟨max threshold 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hBound : Real.log (n : ℝ) ≤
      (c * Real.log 2 / 2) * (n : ℝ) ^ (s - a) := by
    simpa only [Real.norm_of_nonneg (Real.log_nonneg hOne),
      Real.norm_of_nonneg (Real.rpow_nonneg hPos.le _)] using
      hThreshold n ((Nat.le_max_left _ _).trans hn)
  have hBase : Real.logb 2 (n : ℝ) ≤ (c / 2) * (n : ℝ) ^ (s - a) := by
    rw [Real.logb, div_le_iff₀ hlog]
    nlinarith [hBound]
  have hPower : (n : ℝ) ^ a * (n : ℝ) ^ (s - a) = (n : ℝ) ^ s := by
    rw [← Real.rpow_add hPos]
    congr 1
    ring
  refine ⟨hTwo, ?_⟩
  calc
    _ ≤ (n : ℝ) ^ a * ((c / 2) * (n : ℝ) ^ (s - a)) :=
      mul_le_mul_of_nonneg_left hBase (Real.rpow_nonneg hPos.le _)
    _ = c / 2 * (n : ℝ) ^ s := by rw [mul_left_comm, hPower]
    _ < c * (n : ℝ) ^ s :=
      mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hPos _)
private theorem exists_eventual_robustIndexExponent_margin
    (alpha gamma c : ℝ) (hAlpha : alpha < 1 / 2) (hGamma : gamma < 1)
    (hc : 0 < c) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧
        ((n + 1 + Nat.clog 2 (n + 1) *
          (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
            (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) : Nat) : ℝ) <
          c * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨tOne, htOne⟩ := exists_eventual_rpow_logb_margin
    1 ((3 : ℝ) / 2) (c / 32) (by norm_num) (by positivity)
  obtain ⟨tAlpha, htAlpha⟩ := exists_eventual_rpow_logb_margin
    (alpha + 1) ((3 : ℝ) / 2) (c / 12) (by linarith) (by positivity)
  obtain ⟨tGamma, htGamma⟩ := exists_eventual_puncture_floor_linear_margin
    gamma 4 hGamma (by norm_num)
  refine ⟨max tOne (max tAlpha tGamma), ?_⟩
  intro n hn
  have hnOne := (Nat.le_max_left _ _).trans hn
  have hnAlpha := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn)
  have hnGamma := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn)
  obtain ⟨hTwo, hOneMargin⟩ := htOne n hnOne
  obtain ⟨_, hAlphaMargin⟩ := htAlpha n hnAlpha
  obtain ⟨_, hGammaMargin⟩ := htGamma n hnGamma
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hLog : 1 ≤ Real.logb 2 (n : ℝ) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        (by exact_mod_cast hTwo)
  have hClog : (Nat.clog 2 (n + 1) : ℝ) ≤ 3 * Real.logb 2 (n : ℝ) := by
    have h := binaryCeilLog_lt_logb_add_two (by omega : 1 ≤ n)
    linarith
  have hFloor : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) ≤ (n : ℝ) ^ alpha :=
    Nat.floor_le (Real.rpow_nonneg hPos.le _)
  have hQ : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) ≤ n := by
    have h : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) < n := by
      simpa only [show (4 : ℝ) / 4 = 1 by norm_num, one_mul] using hGammaMargin
    exact h.le
  have hPow : (n : ℝ) ^ alpha * n = (n : ℝ) ^ (alpha + 1) := by
    rw [Real.rpow_add hPos, Real.rpow_one]
  have hIndex :
      ((n + 1 + Nat.clog 2 (n + 1) *
        (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
          (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) : Nat) : ℝ) ≤
        2 * n + 12 * (n : ℝ) * Real.logb 2 n +
          3 * (n : ℝ) ^ (alpha + 1) * Real.logb 2 n := by
    push_cast
    calc
      _ ≤ 2 * (n : ℝ) + (3 * Real.logb 2 n) *
          (4 * n + (n : ℝ) ^ alpha * n) := by
        have hInner : 2 * (Nat.floor ((n : ℝ) ^ gamma) : ℝ) + 1 +
            ((Nat.floor ((n : ℝ) ^ alpha) : ℝ) + 1) * n ≤
              4 * n + (n : ℝ) ^ alpha * n := by nlinarith
        exact add_le_add (by linarith) (mul_le_mul hClog hInner
          (by positivity) (by positivity))
      _ = _ := by rw [hPow]; ring
  rw [Real.rpow_one] at hOneMargin
  have hNLog : (n : ℝ) ≤ n * Real.logb 2 n := by
    nlinarith
  have hPowerPos : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hPos _
  refine ⟨hTwo, ?_⟩
  nlinarith [hIndex, hOneMargin, hAlphaMargin]
private theorem exists_eventual_floor_linear_lower
    (a : ℝ) (ha : 0 < a) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ (3 * a / 4) * n ≤ (Nat.floor (a * n) : ℝ) := by
  refine ⟨max (Nat.ceil (4 / a)) 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hLarge : (4 : ℝ) / a ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_max_left _ _).trans hn)
  have hScale : (4 : ℝ) ≤ a * n := by
    have h := (div_le_iff₀ ha).mp hLarge
    nlinarith
  have hFloor := Nat.lt_floor_add_one (a * (n : ℝ))
  exact ⟨hTwo, by nlinarith⟩
private theorem syndromeExponent_lower_of_budgets
    (n p cutoff r q : Nat) (beta rho : ℝ) (hn : 0 < n)
    (hCutoff : 0 < cutoff) (hBeta : 0 < beta) (hRho : 0 < rho)
    (hP : beta / 2 * n ≤ (p : ℝ))
    (hK : (cutoff : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2))
    (hBudget : rho / 4 * n ≤ ((r - (q + p) : Nat) : ℝ)) :
    beta * rho / 8 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
      (((p / cutoff + 1) * (r - (q + p)) : Nat) : ℝ) := by
  have hPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hSqrtPos : 0 < (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hPos _
  have hSquare : (n : ℝ) ^ ((1 : ℝ) / 2) *
      (n : ℝ) ^ ((1 : ℝ) / 2) = n := by
    rw [← Real.rpow_add hPos]
    norm_num
  have hDiv : p < (p / cutoff + 1) * cutoff := by
    calc
      p = p % cutoff + cutoff * (p / cutoff) := (Nat.mod_add_div _ _).symm
      _ < cutoff + cutoff * (p / cutoff) :=
        Nat.add_lt_add_right (Nat.mod_lt _ hCutoff) _
      _ = _ := by ring
  have hRank : beta / 2 * (n : ℝ) ^ ((1 : ℝ) / 2) ≤
      (p / cutoff + 1 : Nat) := by
    apply (mul_le_mul_iff_right₀ hSqrtPos).mp
    calc
      (n : ℝ) ^ ((1 : ℝ) / 2) *
          (beta / 2 * (n : ℝ) ^ ((1 : ℝ) / 2)) = beta / 2 * n := by
        rw [mul_left_comm, hSquare]
      _ ≤ (p : ℝ) := hP
      _ ≤ (p / cutoff + 1 : Nat) * (cutoff : ℝ) := by
        exact_mod_cast hDiv.le
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (p / cutoff + 1 : Nat) := by
        nlinarith [mul_le_mul_of_nonneg_left hK
          (Nat.cast_nonneg (p / cutoff + 1) : (0 : ℝ) ≤ (p / cutoff + 1 : Nat))]
  have hPower : (n : ℝ) ^ ((1 : ℝ) / 2) * n =
      (n : ℝ) ^ ((3 : ℝ) / 2) := by
    calc
      _ = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (((1 : ℝ) / 2) + 1) := (Real.rpow_add hPos _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    beta * rho / 8 * (n : ℝ) ^ ((3 : ℝ) / 2) =
        (beta / 2 * (n : ℝ) ^ ((1 : ℝ) / 2)) * (rho / 4 * n) := by
      rw [← hPower]
      ring
    _ ≤ (p / cutoff + 1 : Nat) * ((r - (q + p) : Nat) : ℝ) :=
      mul_le_mul hRank hBudget (by positivity) (by positivity)
    _ = _ := by push_cast; rfl
private theorem exists_eventual_floored_syndromeExponent_lower
    (alpha gamma beta rho : ℝ) (hAlphaNonneg : 0 ≤ alpha)
    (hAlpha : alpha ≤ 1 / 2) (hGamma : gamma < 1)
    (hBeta : 0 < beta) (hRho : 0 < rho) (hBetaRho : beta ≤ rho / 4) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ 0 < Nat.floor ((n : ℝ) ^ alpha) ∧
        Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n) ≤ Nat.floor (rho * n) ∧
        beta * rho / 8 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
          (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
            (Nat.floor (rho * n) -
              (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n))) : Nat) : ℝ) := by
  obtain ⟨tP, htP⟩ := exists_eventual_floor_linear_lower beta hBeta
  obtain ⟨tR, htR⟩ := exists_eventual_floor_linear_lower rho hRho
  obtain ⟨tQ, htQ⟩ := exists_eventual_puncture_floor_linear_margin gamma rho hGamma hRho
  refine ⟨max tP (max tR tQ), ?_⟩
  intro n hn
  obtain ⟨hTwo, hPLower⟩ := htP n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, hRLower⟩ := htR n
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn))
  obtain ⟨_, hQUpper⟩ := htQ n
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hPUpper : (Nat.floor (beta * n) : ℝ) ≤ rho / 4 * n := by
    have hFloor := Nat.floor_le (show 0 ≤ beta * (n : ℝ) by positivity)
    nlinarith
  have hQPReal : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) +
      (Nat.floor (beta * n) : ℝ) ≤ (Nat.floor (rho * n) : ℝ) := by
    nlinarith
  have hQP : Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n) ≤
      Nat.floor (rho * n) := by exact_mod_cast hQPReal
  have hBudget : rho / 4 * n ≤
      ((Nat.floor (rho * n) -
        (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n)) : Nat) : ℝ) := by
    rw [Nat.cast_sub hQP, Nat.cast_add]
    nlinarith
  have hKPos : 0 < Nat.floor ((n : ℝ) ^ alpha) := by
    have h := Nat.floor_mono (Real.one_le_rpow hOne hAlphaNonneg)
    have hOneFloor : 1 ≤ Nat.floor ((n : ℝ) ^ alpha) := by
      simpa only [Nat.floor_one] using h
    omega
  have hK : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 2) :=
    (Nat.floor_le (Real.rpow_nonneg hPos.le _)).trans
      (Real.rpow_le_rpow_of_exponent_le hOne hAlpha)
  refine ⟨hTwo, hKPos, hQP, ?_⟩
  exact syndromeExponent_lower_of_budgets n _ _ _ _ beta rho
    (by omega) hKPos hBeta hRho (by nlinarith) hK hBudget
private theorem exists_eventual_robustIndexExponent_add_two_le_syndrome
    (alpha gamma beta rho : ℝ) (hAlphaNonneg : 0 ≤ alpha)
    (hAlpha : alpha < 1 / 2) (hGamma : gamma < 1)
    (hBeta : 0 < beta) (hRho : 0 < rho) (hBetaRho : beta ≤ rho / 4) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      n + 1 + Nat.clog 2 (n + 1) *
          (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
            (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) + 2 ≤
        (Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
          (Nat.floor (rho * n) -
            (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n))) := by
  obtain ⟨tI, htI⟩ := exists_eventual_robustIndexExponent_margin
    alpha gamma (beta * rho / 16) hAlpha hGamma (by positivity)
  obtain ⟨tD, htD⟩ := exists_eventual_floored_syndromeExponent_lower
    alpha gamma beta rho hAlphaNonneg hAlpha.le hGamma hBeta hRho hBetaRho
  refine ⟨max tI (max tD (Nat.ceil (32 / (beta * rho)))), ?_⟩
  intro n hn
  obtain ⟨hTwo, hIndex⟩ := htI n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, _, _, hDen⟩ := htD n
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hLarge : (32 : ℝ) / (beta * rho) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hPowN : (n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hOne (by norm_num)
  have hMarginTwo : (2 : ℝ) ≤ beta * rho / 16 * (n : ℝ) ^ ((3 : ℝ) / 2) := by
    have hScale := (div_le_iff₀ (show 0 < beta * rho by positivity)).mp hLarge
    have hMul := mul_le_mul_of_nonneg_left hPowN
      (show 0 ≤ beta * rho / 16 by positivity)
    nlinarith
  have hReal :
      ((n + 1 + Nat.clog 2 (n + 1) *
        (2 * Nat.floor ((n : ℝ) ^ gamma) + 1 +
          (Nat.floor ((n : ℝ) ^ alpha) + 1) * n) : Nat) : ℝ) + 2 ≤
        (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
          (Nat.floor (rho * n) -
            (Nat.floor ((n : ℝ) ^ gamma) + Nat.floor (beta * n))) : Nat) : ℝ) := by
    nlinarith [hIndex, hDen, hMarginTwo]
  exact_mod_cast hReal
private theorem exists_eventual_rpow_margin
    (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      2 ≤ n ∧ (n : ℝ) ^ a < c * (n : ℝ) ^ b := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).eventually
    (gt_mem_nhds hc)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨t, ht⟩ := eventually_atTop.mp hNat
  refine ⟨max t 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨hTwo, ?_⟩
  calc
    (n : ℝ) ^ a = (n : ℝ) ^ (-(b - a)) * (n : ℝ) ^ b := by
      rw [← Real.rpow_add hPos]
      congr 1
      ring
    _ < c * (n : ℝ) ^ b := mul_lt_mul_of_pos_right
      (ht n ((Nat.le_max_left _ _).trans hn)) (Real.rpow_pos_of_pos hPos _)
private theorem exists_eventual_floored_robustness_weight_budget
    (epsilon beta : ℝ) (hEpsilon : 0 < epsilon) (hBeta : 0 < beta) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) <
        (Nat.floor (beta * n) + 1) *
          (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) + 1) := by
  obtain ⟨t, ht⟩ := exists_eventual_rpow_margin
    ((3 : ℝ) / 2 - epsilon) (1 + ((1 : ℝ) / 2 - epsilon / 2))
    beta (by linarith) hBeta
  refine ⟨t, ?_⟩
  intro n hn
  obtain ⟨hTwo, hSmall⟩ := ht n hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP : beta * n < (Nat.floor (beta * n) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hK : (n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2) <
      (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hPower : (n : ℝ) ^ (1 + ((1 : ℝ) / 2 - epsilon / 2)) =
      (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2) := by
    rw [Real.rpow_add hPos, Real.rpow_one]
  have hProduct : beta * (n : ℝ) ^ (1 + ((1 : ℝ) / 2 - epsilon / 2)) <
      ((Nat.floor (beta * n) : ℝ) + 1) *
        ((Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) : ℝ) + 1) := by
    rw [hPower, ← mul_assoc]
    exact mul_lt_mul hP hK.le (by positivity) (by positivity)
  have hFloor := Nat.floor_le
    (Real.rpow_nonneg hPos.le ((3 : ℝ) / 2 - epsilon))
  have hResult : (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) : ℝ) <
      ((Nat.floor (beta * n) : ℝ) + 1) *
        ((Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)) : ℝ) + 1) :=
    hFloor.trans_lt (hSmall.trans hProduct)
  exact_mod_cast hResult
private theorem exists_eventual_floored_robustness_distance_budgets
    (alpha gamma beta delta : ℝ) (hAlphaNonneg : 0 ≤ alpha)
    (hAlpha : alpha < 1) (hGamma : gamma < 1)
    (hBeta : 0 < beta) (hDelta : 0 < delta) (hBetaDelta : beta ≤ delta / 8) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      let p := Nat.floor (beta * n)
      let cutoff := Nat.floor ((n : ℝ) ^ alpha)
      let q := Nat.floor ((n : ℝ) ^ gamma)
      let distance := Nat.floor (delta * n)
      0 < cutoff ∧ q ≤ n ∧ cutoff ≤ n ∧
        (p / cutoff + 1) * cutoff < distance - q ∧
        2 * p ≤ distance - q := by
  obtain ⟨tD, htD⟩ := exists_eventual_floor_linear_lower delta hDelta
  obtain ⟨tK, htK⟩ := exists_eventual_puncture_floor_linear_margin
    alpha (min delta 4) hAlpha (lt_min hDelta (by norm_num))
  obtain ⟨tQ, htQ⟩ := exists_eventual_puncture_floor_linear_margin
    gamma (min delta 4) hGamma (lt_min hDelta (by norm_num))
  refine ⟨max tD (max tK tQ), ?_⟩
  intro n hn
  dsimp only
  obtain ⟨hTwo, hD⟩ := htD n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, hK⟩ := htK n
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn))
  obtain ⟨_, hQ⟩ := htQ n
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn))
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hKPos : 0 < Nat.floor ((n : ℝ) ^ alpha) := by
    have h := Nat.floor_mono (Real.one_le_rpow hOne hAlphaNonneg)
    have hOneFloor : 1 ≤ Nat.floor ((n : ℝ) ^ alpha) := by
      simpa only [Nat.floor_one] using h
    omega
  have hP := Nat.floor_le (show 0 ≤ beta * (n : ℝ) by positivity)
  have hMinD := min_le_left delta (4 : ℝ)
  have hMinFour := min_le_right delta (4 : ℝ)
  have hKDistance : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) < delta / 4 * n := by
    nlinarith
  have hQDistance : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) < delta / 4 * n := by
    nlinarith
  have hKN : Nat.floor ((n : ℝ) ^ alpha) ≤ n := by
    have h : (Nat.floor ((n : ℝ) ^ alpha) : ℝ) ≤ n := by nlinarith
    exact_mod_cast h
  have hQN : Nat.floor ((n : ℝ) ^ gamma) ≤ n := by
    have h : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) ≤ n := by nlinarith
    exact_mod_cast h
  have hQD : Nat.floor ((n : ℝ) ^ gamma) ≤ Nat.floor (delta * n) := by
    have h : (Nat.floor ((n : ℝ) ^ gamma) : ℝ) ≤
        (Nat.floor (delta * n) : ℝ) := by nlinarith
    exact_mod_cast h
  have hRankLe : (Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
      Nat.floor ((n : ℝ) ^ alpha) ≤
        Nat.floor (beta * n) + Nat.floor ((n : ℝ) ^ alpha) := by
    have h := Nat.div_mul_le_self (Nat.floor (beta * n))
      (Nat.floor ((n : ℝ) ^ alpha))
    nlinarith
  have hRankReal :
      (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
        Nat.floor ((n : ℝ) ^ alpha) : Nat) : ℝ) <
      ((Nat.floor (delta * n) - Nat.floor ((n : ℝ) ^ gamma) : Nat) : ℝ) := by
    rw [Nat.cast_sub hQD]
    have hRankCast : (((Nat.floor (beta * n) / Nat.floor ((n : ℝ) ^ alpha) + 1) *
        Nat.floor ((n : ℝ) ^ alpha) : Nat) : ℝ) ≤
        (Nat.floor (beta * n) : ℝ) + (Nat.floor ((n : ℝ) ^ alpha) : ℝ) := by
      exact_mod_cast hRankLe
    nlinarith
  have hCoverReal : (2 : ℝ) * (Nat.floor (beta * n) : ℝ) ≤
      ((Nat.floor (delta * n) - Nat.floor ((n : ℝ) ^ gamma) : Nat) : ℝ) := by
    rw [Nat.cast_sub hQD]
    nlinarith
  exact ⟨hKPos, hQN, hKN, by exact_mod_cast hRankReal,
    by exact_mod_cast hCoverReal⟩
private theorem exists_eventual_source_robustness_floor_budgets
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hRho : 0 < rho) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      let beta := min delta rho / 8
      let p := Nat.floor (beta * n)
      let cutoff := Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2))
      let q := Nat.floor ((n : ℝ) ^ gamma)
      let distance := Nat.floor (delta * n)
      let w := Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon))
      0 < cutoff ∧ q ≤ n ∧ cutoff ≤ n ∧
        w < (p + 1) * (cutoff + 1) ∧
        (p / cutoff + 1) * cutoff < distance - q ∧
        2 * p ≤ distance - q := by
  have hBeta : 0 < min delta rho / 8 := by
    exact div_pos (lt_min hDelta hRho) (by norm_num)
  have hBetaDelta : min delta rho / 8 ≤ delta / 8 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  obtain ⟨tW, htW⟩ := exists_eventual_floored_robustness_weight_budget
    epsilon (min delta rho / 8) hEpsilon hBeta
  obtain ⟨tD, htD⟩ := exists_eventual_floored_robustness_distance_budgets
    ((1 : ℝ) / 2 - epsilon / 2) gamma (min delta rho / 8) delta
    (by linarith) (by linarith) hGamma hBeta hDelta hBetaDelta
  refine ⟨max tW tD, ?_⟩
  intro n hn
  obtain ⟨hK, hQ, hKN, hRank, hCover⟩ :=
    htD n ((Nat.le_max_right _ _).trans hn)
  exact ⟨hK, hQ, hKN, htW n ((Nat.le_max_left _ _).trans hn), hRank, hCover⟩
end RobustnessIndexBounds
private theorem lowWeight_binomialWeight_ge
    {n m k : Nat} (hk : k ≤ m) (hhalf : 2 * m ≤ n) :
    m ^ m * (n - m) ^ (n - m) ≤
      m ^ k * (n - m) ^ (n - k) := by
  have hm : m = k + (m - k) := by omega
  have hnk : n - k = (n - m) + (m - k) := by omega
  have hpow : m ^ (m - k) ≤ (n - m) ^ (m - k) :=
    pow_le_pow_left₀ (Nat.zero_le _) (by omega) _
  have hsplitM : m ^ m = m ^ k * m ^ (m - k) := by
    calc
      m ^ m = m ^ (k + (m - k)) := congrArg (m ^ ·) hm
      _ = m ^ k * m ^ (m - k) := pow_add _ _ _
  have hsplitN :
      (n - m) ^ (n - k) =
        (n - m) ^ (n - m) * (n - m) ^ (m - k) := by
    calc
      (n - m) ^ (n - k) =
          (n - m) ^ ((n - m) + (m - k)) :=
            congrArg ((n - m) ^ ·) hnk
      _ = (n - m) ^ (n - m) * (n - m) ^ (m - k) := pow_add _ _ _
  calc
    m ^ m * (n - m) ^ (n - m) =
        (m ^ k * m ^ (m - k)) * (n - m) ^ (n - m) := by
          rw [hsplitM]
    _ ≤ (m ^ k * (n - m) ^ (m - k)) * (n - m) ^ (n - m) :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ hpow)
    _ = m ^ k * (n - m) ^ (n - k) := by
          rw [hsplitN]
          ring
private theorem binaryHammingBall_mul_entropyDenominator_le
    (n m : Nat) (hhalf : 2 * m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), Nat.choose n k) *
        (m ^ m * (n - m) ^ (n - m)) ≤ n ^ n := by
  have hmle : m ≤ n := by omega
  have hrange : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    exact Finset.range_mono (by omega)
  calc
    (∑ k ∈ Finset.range (m + 1), Nat.choose n k) *
        (m ^ m * (n - m) ^ (n - m)) =
        ∑ k ∈ Finset.range (m + 1),
          Nat.choose n k * (m ^ m * (n - m) ^ (n - m)) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          Nat.choose n k * (m ^ k * (n - m) ^ (n - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact Nat.mul_le_mul_left _
            (lowWeight_binomialWeight_ge
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hhalf)
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          Nat.choose n k * (m ^ k * (n - m) ^ (n - k)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hrange
          intro k _ _
          exact Nat.zero_le _
    _ = (m + (n - m)) ^ n := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k _
          simp only [Nat.cast_id]
          ac_rfl
    _ = n ^ n := by
          congr 1
          omega
private theorem natEntropyRay_eq_mul_binEntropy
    (n m : Nat) (hm : 0 < m) (hmn : m < n) :
    (n : ℝ) * Real.log n -
        (m : ℝ) * Real.log m -
        ((n - m : Nat) : ℝ) *
          Real.log ((n - m : Nat) : ℝ) =
      (n : ℝ) * Real.binEntropy ((m : ℝ) / n) := by
  have hn : 0 < n := lt_trans hm hmn
  have hsub : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hsubR : ((n - m : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsub
  have hcastSub : ((n - m : Nat) : ℝ) = (n : ℝ) - m := by
    rw [Nat.cast_sub hmn.le]
  have hone_sub : 1 - (m : ℝ) / n =
      ((n - m : Nat) : ℝ) / n := by
    rw [hcastSub]
    field_simp [hnR]
  have hinv_m : ((m : ℝ) / n)⁻¹ = (n : ℝ) / m := by
    field_simp [hnR, hmR]
  have hinv_sub : (((n - m : Nat) : ℝ) / n)⁻¹ =
      (n : ℝ) / (n - m) := by
    rw [hcastSub]
    field_simp [hnR, hsubR]
  have hlog_sub : Real.log ((n : ℝ) / ((n : ℝ) - m)) =
      Real.log (n : ℝ) - Real.log ((n - m : Nat) : ℝ) := by
    rw [← hcastSub]
    exact Real.log_div hnR hsubR
  unfold Real.binEntropy
  rw [hinv_m, hone_sub, hinv_sub,
    Real.log_div hnR hmR, hlog_sub]
  rw [hcastSub]
  field_simp [hnR]
  ring
private theorem binaryHammingBall_le_exp_binEntropy
    (n m : Nat) (hm : 0 < m) (hhalf : 2 * m ≤ n) :
    (((∑ k ∈ Finset.range (m + 1), Nat.choose n k) : Nat) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((m : ℝ) / n)) := by
  let volume := ∑ k ∈ Finset.range (m + 1), Nat.choose n k
  have hmn : m < n := by omega
  have hsub : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hvolumeOne : 1 ≤ volume := by
    have h := Finset.single_le_sum
      (fun k _ => Nat.zero_le (Nat.choose n k))
      (show 0 ∈ Finset.range (m + 1) by simp)
    simpa [volume] using h
  have hvolumePos : (0 : ℝ) < volume := by
    exact_mod_cast (show 0 < volume by omega)
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsubPos : (0 : ℝ) < (n - m : Nat) := by exact_mod_cast hsub
  have hdenPos :
      (0 : ℝ) < (m : ℝ) ^ m *
        (((n - m : Nat) : ℝ) ^ (n - m)) := by positivity
  have hfinite :
      (volume : ℝ) *
          ((m : ℝ) ^ m * (((n - m : Nat) : ℝ) ^ (n - m))) ≤
        (n : ℝ) ^ n := by
    dsimp [volume]
    exact_mod_cast binaryHammingBall_mul_entropyDenominator_le n m hhalf
  have hlog := Real.log_le_log
    (mul_pos hvolumePos hdenPos) hfinite
  rw [Real.log_mul (ne_of_gt hvolumePos) (ne_of_gt hdenPos),
    Real.log_mul (pow_ne_zero _ (ne_of_gt hmPos))
      (pow_ne_zero _ (ne_of_gt hsubPos)),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlogVolume :
      Real.log (volume : ℝ) ≤
        (n : ℝ) * Real.binEntropy ((m : ℝ) / n) := by
    rw [← natEntropyRay_eq_mul_binEntropy n m hm hmn]
    linarith
  calc
    (volume : ℝ) = Real.exp (Real.log (volume : ℝ)) :=
      (Real.exp_log hvolumePos).symm
    _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((m : ℝ) / n)) :=
      Real.exp_le_exp.mpr hlogVolume
private theorem binaryHammingBall_le_exp_binEntropy_of_radius_le
    (n m : Nat) (delta : ℝ) (hm : 0 < m) (hhalf : 2 * m ≤ n)
    (hradius : (m : ℝ) / n ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    (((∑ k ∈ Finset.range (m + 1), Nat.choose n k) : Nat) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy delta) := by
  have hn : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hradiusNonnegative : (0 : ℝ) ≤ (m : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) hnReal.le
  have hradiusHalf : (m : ℝ) / n ≤ (2 : ℝ)⁻¹ := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    apply (div_le_iff₀ hnReal).2
    have hhalfReal : (2 : ℝ) * m ≤ n := by exact_mod_cast hhalf
    nlinarith
  have hdeltaNonnegative : 0 ≤ delta :=
    hradiusNonnegative.trans hradius
  have hentropy :
      Real.binEntropy ((m : ℝ) / n) ≤ Real.binEntropy delta :=
    Real.binEntropy_strictMonoOn.monotoneOn
      ⟨hradiusNonnegative, hradiusHalf⟩
      ⟨hdeltaNonnegative, by simpa only [inv_eq_one_div] using hdeltaHalf⟩
      hradius
  exact (binaryHammingBall_le_exp_binEntropy n m hm hhalf).trans
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hentropy hnReal.le))
private theorem binaryHammingBall_le_exp_binEntropy_ceilRadius
    (n : Nat) (delta : ℝ) (hn : 0 < n)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * n)) :
    (((∑ k ∈ Finset.range (Nat.ceil (delta * n)),
        Nat.choose n k) : Nat) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy delta) := by
  let m := Nat.ceil (delta * n) - 1
  have hm : 0 < m := by dsimp [m]; omega
  have hceilPositive : 0 ≤ delta * (n : ℝ) :=
    mul_nonneg hdeltaPositive.le (Nat.cast_nonneg n)
  have hceilBound :
      (Nat.ceil (delta * n) : ℝ) < delta * n + 1 :=
    Nat.ceil_lt_add_one hceilPositive
  have hmCast : (m : ℝ) = (Nat.ceil (delta * n) : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil (delta * n))]
    norm_num
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmBelow : (m : ℝ) < delta * n := by linarith
  have hradius : (m : ℝ) / n ≤ delta := by
    apply (div_le_iff₀ hnReal).2
    exact hmBelow.le
  have hhalfReal : (2 : ℝ) * m < n := by
    have hdeltaBound : delta * (n : ℝ) < (1 / 2 : ℝ) * n :=
      mul_lt_mul_of_pos_right hdeltaHalf hnReal
    nlinarith
  have hhalf : 2 * m ≤ n := by
    exact_mod_cast hhalfReal.le
  have hbound := binaryHammingBall_le_exp_binEntropy_of_radius_le
    n m delta hm hhalf hradius hdeltaHalf.le
  simpa only [m, Nat.sub_add_cancel (by omega : 1 ≤ Nat.ceil (delta * n))]
    using hbound
private theorem fixedRowCombinationMap_surjective
    {row col : Type v} [Fintype row]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    Function.Surjective (fixedRowCombinationMap (col := col) coefficients) := by
  have hexists : ∃ i, coefficients i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hcoefficients
    funext i
    exact hzero i
  obtain ⟨i, hi⟩ := hexists
  intro y
  let M : Matrix row col (ZMod 2) := fun r c =>
    if r = i then (coefficients i)⁻¹ * y c else 0
  refine ⟨M, ?_⟩
  funext c
  simp [fixedRowCombinationMap, M, Matrix.vecMul, dotProduct, hi]
private theorem finrank_ker_fixedRowCombinationMap
    {row col : Type v} [Fintype row] [Fintype col]
    {coefficients : row → ZMod 2} (hcoefficients : coefficients ≠ 0) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (fixedRowCombinationMap (col := col) coefficients)) =
      Fintype.card row * Fintype.card col - Fintype.card col := by
  let f := fixedRowCombinationMap (col := col) coefficients
  have hSurjective : Function.Surjective f :=
    fixedRowCombinationMap_surjective (col := col) hcoefficients
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr hSurjective
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  norm_num [f, fixedRowCombinationMap, Module.finrank_matrix] at hRankNullity
  have hKernel := Nat.eq_sub_of_add_eq (by
    simpa [Nat.add_comm] using hRankNullity)
  simpa [f, Nat.mul_comm] using hKernel
private theorem card_binaryMatrix
    (row col : Type v) [Fintype row] [Fintype col] :
    Fintype.card (Matrix row col (ZMod 2)) =
      2 ^ (Fintype.card row * Fintype.card col) := by
  rw [@Module.card_eq_pow_finrank (ZMod 2) (Matrix row col (ZMod 2))
    _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase]
  congr 1
  norm_num [Module.finrank_matrix]
private theorem firstDistanceBad_covers_not_codeA_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeA distance) :
    ∃ index :
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      firstDistanceBad index sample := by
  obtain ⟨coefficients, hcoefficients, target, htarget, hvecMul⟩ :=
    exists_rowCombination_lowWeight_of_not_codeA_distance
      sample hDistance
  exact ⟨⟨⟨coefficients, hcoefficients⟩, ⟨target, htarget⟩⟩,
    hvecMul⟩
private theorem card_firstDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (firstDistanceBad (B := B) index)).card =
      2 ^ (r * Fintype.card A - Fintype.card A) *
        2 ^ (r * Fintype.card B) := by
  obtain ⟨base, hbase⟩ :=
    fixedRowCombinationMap_surjective
      (col := A) index.1.2 index.2.1.1
  have hFiberEquiv :
      {matrix : Matrix (ULift.{v} (Fin r)) A (ZMod 2) //
        Matrix.vecMul index.1.1 matrix = index.2.1.1} ≃
        LinearMap.ker
          (fixedRowCombinationMap (col := A) index.1.1) := by
    change
      {matrix : Matrix (ULift.{v} (Fin r)) A (ZMod 2) //
        fixedRowCombinationMap index.1.1 matrix = index.2.1.1} ≃ _
    rw [← hbase]
    exact linearFiberEquivKer
      (fixedRowCombinationMap (col := A) index.1.1) base
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (firstDistanceBadEventEquiv index),
    Fintype.card_prod, Fintype.card_congr hFiberEquiv]
  rw [@Module.card_eq_pow_finrank (ZMod 2)
    (LinearMap.ker
      (fixedRowCombinationMap (col := A) index.1.1)) _ _ _ _ _,
    @Module.card_eq_pow_finrank (ZMod 2)
      (Matrix (ULift.{v} (Fin r)) B (ZMod 2)) _ _ _ _ _]
  have hbaseCard : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbaseCard,
    finrank_ker_fixedRowCombinationMap index.1.2,
    Module.finrank_matrix]
  simp
private theorem card_nonzeroBinaryRowCombination
    (row : Type v) [Fintype row] :
    Fintype.card {coefficients : row → ZMod 2 // coefficients ≠ 0} =
      2 ^ Fintype.card row - 1 := by
  rw [Fintype.card_subtype_compl
      (fun coefficients : row → ZMod 2 => coefficients = 0),
    Fintype.card_subtype_eq, Fintype.card_fun]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase]
private theorem sum_card_firstDistanceBad
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index :
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      (eventFinset (firstDistanceBad (B := B) index)).card =
        ((2 ^ r - 1) *
          Fintype.card {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) := by
  have hEach : ∀ index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      (eventFinset (firstDistanceBad (B := B) index)).card =
        2 ^ (r * Delta - Delta) * 2 ^ (r * Delta) := by
    intro index
    rw [card_firstDistanceBad]
    simp only [hA, hB]
  have hIndex :
      Fintype.card
        ({coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) =
        (2 ^ r - 1) *
          Fintype.card
            {target : BinaryLowWeightWords A distance // target.1 ≠ 0} := by
    have hCoefficients :
        Fintype.card
          {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} =
          2 ^ r - 1 := by
      rw [Fintype.card_subtype_compl
          (fun coefficients : ULift.{v} (Fin r) → ZMod 2 =>
            coefficients = 0),
        Fintype.card_subtype_eq, Fintype.card_fun]
      have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      rw [hbase, Fintype.card_ulift, Fintype.card_fin]
    rw [Fintype.card_prod, hCoefficients]
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, hIndex, nsmul_eq_mul]
  norm_num
private theorem sum_card_firstDistanceBad_le
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index :
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0},
      (eventFinset (firstDistanceBad (B := B) index)).card ≤
        ((2 ^ r - 1) *
          (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) := by
  rw [sum_card_firstDistanceBad hA hB]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  calc
    Fintype.card
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0} ≤
        Fintype.card (BinaryLowWeightWords A distance) :=
      Fintype.card_subtype_le _
    _ = ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card A) weight :=
      card_binaryLowWeightWords A distance
    _ = ∑ weight ∈ Finset.range distance, Nat.choose Delta weight := by
      rw [hA]
private theorem card_rankDependencyIndex
    (row : Type v) [Fintype row] :
    Fintype.card (Bool ×
      {coefficients : row → ZMod 2 // coefficients ≠ 0}) =
      2 * (2 ^ Fintype.card row - 1) := by
  rw [Fintype.card_prod, card_nonzeroBinaryRowCombination]
  norm_num
private theorem rankDependencyBad_covers_not_fullRowRank
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hFull : ¬sample.HasFullRowRank) :
    ∃ index : Bool ×
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0},
      rankDependencyBad index sample := by
  rcases exists_rankFailureWitness_of_not_fullRowRank hFull with
    ⟨coefficients, hcoefficients, hvanishes⟩ |
      ⟨coefficients, hcoefficients, hvanishes⟩
  · exact ⟨⟨false, ⟨coefficients, hcoefficients⟩⟩, hvanishes⟩
  · exact ⟨⟨true, ⟨coefficients, hcoefficients⟩⟩, hvanishes⟩
private theorem card_randomLocalCodeSample
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    Fintype.card (RandomLocalCodeSample r A B) =
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  change Fintype.card
      (Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
        Matrix (ULift.{v} (Fin r)) B (ZMod 2)) = _
  rw [@Module.card_eq_pow_finrank (ZMod 2)
    (Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
      Matrix (ULift.{v} (Fin r)) B (ZMod 2)) _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase, Module.finrank_prod, Module.finrank_matrix,
    Module.finrank_matrix, pow_add]
  simp [hA, hB]
private theorem fixedColumnCombinationMap_surjective
    {row col : Type v} [Fintype col]
    {target : col → ZMod 2} (htarget : target ≠ 0) :
    Function.Surjective (fixedColumnCombinationMap (row := row) target) := by
  have hexists : ∃ j, target j ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply htarget
    funext j
    exact hzero j
  obtain ⟨j, hj⟩ := hexists
  intro y
  let M : Matrix row col (ZMod 2) := fun i k =>
    if k = j then y i * (target j)⁻¹ else 0
  refine ⟨M, ?_⟩
  funext i
  simp [fixedColumnCombinationMap, M, Matrix.mulVec, dotProduct, hj]
private theorem finrank_ker_fixedColumnCombinationMap
    {row col : Type v} [Fintype row] [Fintype col]
    {target : col → ZMod 2} (htarget : target ≠ 0) :
    Module.finrank (ZMod 2)
        (LinearMap.ker
          (fixedColumnCombinationMap (row := row) target)) =
      Fintype.card row * Fintype.card col - Fintype.card row := by
  let f := fixedColumnCombinationMap (row := row) target
  have hSurjective : Function.Surjective f :=
    fixedColumnCombinationMap_surjective (row := row) htarget
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr hSurjective
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  norm_num [f, fixedColumnCombinationMap,
    Module.finrank_matrix] at hRankNullity
  have hKernel := Nat.eq_sub_of_add_eq (by
    simpa [Nat.add_comm] using hRankNullity)
  simpa [f, Nat.mul_comm] using hKernel
private theorem secondDistanceBad_covers_not_codeB_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeB distance) :
    ∃ index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0},
      secondDistanceBad (A := A) index sample := by
  obtain ⟨target, htarget, hkernel⟩ :=
    exists_lowWeight_kernel_of_not_codeB_distance sample hDistance
  exact ⟨⟨target, htarget⟩, hkernel⟩
private theorem card_secondDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (secondDistanceBad (r := r) (A := A) index)).card =
      2 ^ (r * Fintype.card A) *
        2 ^ (r * Fintype.card B - r) := by
  rw [eventFinset, ← Fintype.card_subtype,
    Fintype.card_congr (secondDistanceBadEventEquiv (r := r) index),
    Fintype.card_prod]
  rw [@Module.card_eq_pow_finrank (ZMod 2)
      (Matrix (ULift.{v} (Fin r)) A (ZMod 2)) _ _ _ _ _,
    @Module.card_eq_pow_finrank (ZMod 2)
      (LinearMap.ker
        (fixedColumnCombinationMap
          (row := ULift.{v} (Fin r)) index.1.1)) _ _ _ _ _]
  have hbaseCard : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbaseCard, Module.finrank_matrix,
    finrank_ker_fixedColumnCombinationMap index.2]
  simp
private theorem sum_card_secondDistanceBad_le
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0},
      (eventFinset
        (secondDistanceBad (r := r) (A := A) index)).card ≤
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) := by
  have hEach : ∀ index :
      {target : BinaryLowWeightWords B distance // target.1 ≠ 0},
      (eventFinset
        (secondDistanceBad (r := r) (A := A) index)).card =
        2 ^ (r * Delta) * 2 ^ (r * Delta - r) := by
    intro index
    rw [card_secondDistanceBad (r := r)]
    simp only [hA, hB]
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply Nat.mul_le_mul_right
  calc
    Fintype.card
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0} ≤
        Fintype.card (BinaryLowWeightWords B distance) :=
      Fintype.card_subtype_le _
    _ = ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card B) weight :=
      card_binaryLowWeightWords B distance
    _ = ∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight := by
      rw [hB]
private theorem card_eventFinset_comp_equiv
    {Omega : Type u} {Omega' : Type v} [Fintype Omega] [Fintype Omega']
    (equiv : Omega ≃ Omega') (event : Omega' → Prop)
    [DecidablePred event] [DecidablePred (fun sample => event (equiv sample))] :
    (eventFinset (fun sample => event (equiv sample))).card =
      (eventFinset event).card := by
  rw [eventFinset, ← Fintype.card_subtype,
    eventFinset, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv equiv (by simp)
private theorem card_eventFinset_congr
    {Omega : Type u} [Fintype Omega]
    (event event' : Omega → Prop)
    [DecidablePred event] [DecidablePred event']
    (hiff : ∀ sample, event sample ↔ event' sample) :
    (eventFinset event).card = (eventFinset event').card := by
  have heq : eventFinset event = eventFinset event' := by
    ext sample
    rw [mem_eventFinset, mem_eventFinset]
    exact hiff sample
  rw [heq]
private theorem card_swapped_secondDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (fun sample : RandomLocalCodeSample r A B =>
      secondDistanceBad (r := r) (A := B) index
        (swapRandomLocalCodeSample r A B sample))).card =
      (eventFinset
        (secondDistanceBad (r := r) (A := B) index)).card := by
  exact card_eventFinset_comp_equiv
    (swapRandomLocalCodeSample r A B)
    (secondDistanceBad (r := r) (A := B) index)
private theorem card_swapped_firstDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (fun sample : RandomLocalCodeSample r A B =>
      firstDistanceBad (B := A) index
        (swapRandomLocalCodeSample r A B sample))).card =
      (eventFinset (firstDistanceBad (B := A) index)).card := by
  exact card_eventFinset_comp_equiv
    (swapRandomLocalCodeSample r A B)
    (firstDistanceBad (B := A) index)
private theorem dual_dual_carrier_eq
    {F : Type u} {I : Type v} [Field F] [Fintype F] [Fintype I]
    (code : LinearCode F I) :
    code.dual.dual.carrier = code.carrier := by
  let pairing :=
    LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := I))
  have hNondegenerate : pairing.Nondegenerate :=
    (wordPairing_nondegenerate (F := F) (ι := I)).flip
  have hRefl : pairing.IsRefl := by
    intro x y hxy
    change wordPairing (F := F) (ι := I) y x = 0 at hxy
    change wordPairing (F := F) (ι := I) x y = 0
    rw [wordPairing_apply, dotProduct_comm]
    exact hxy
  change pairing.orthogonal (pairing.orthogonal code.carrier) = code.carrier
  exact pairing.orthogonal_orthogonal hNondegenerate hRefl code.carrier
private theorem card_simultaneousDistanceBad_rank
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (distance := distance) (A := A) (B := B) (Sum.inl index))).card =
      (eventFinset (rankDependencyBad (A := A) (B := B) index)).card := by
  apply card_eventFinset_congr
  intro sample
  rfl
private theorem card_simultaneousDistanceBad_first
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (B := B) (Sum.inr (Sum.inl index)))).card =
      (eventFinset (firstDistanceBad (B := B) index)).card := by
  apply card_eventFinset_congr
  intro sample
  rfl
private theorem card_simultaneousDistanceBad_second
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (r := r) (A := A) (Sum.inr (Sum.inr (Sum.inl index))))).card =
      (eventFinset (secondDistanceBad (r := r) (A := A) index)).card := by
  apply card_eventFinset_congr
  intro sample
  rfl
private theorem card_simultaneousDistanceBad_firstDual
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (r := r) (B := B)
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl index)))))).card =
      (eventFinset
        (secondDistanceBad (r := r) (A := B) index)).card := by
  calc
    _ = (eventFinset (fun sample : RandomLocalCodeSample r A B =>
          secondDistanceBad (r := r) (A := B) index
            (swapRandomLocalCodeSample r A B sample))).card := by
      apply card_eventFinset_congr
      intro sample
      rfl
    _ = _ := card_swapped_secondDistanceBad index
private theorem card_simultaneousDistanceBad_secondDual
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    (eventFinset (simultaneousDistanceBad
      (A := A) (Sum.inr (Sum.inr (Sum.inr (Sum.inr index)))))).card =
      (eventFinset (firstDistanceBad (B := A) index)).card := by
  calc
    _ = (eventFinset (fun sample : RandomLocalCodeSample r A B =>
          firstDistanceBad (B := A) index
            (swapRandomLocalCodeSample r A B sample))).card := by
      apply card_eventFinset_congr
      intro sample
      rfl
    _ = _ := card_swapped_firstDistanceBad index
private theorem simultaneousDistanceBad_covers
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hgood : ¬(sample.HasFullRowRank ∧
      HasMinimumDistanceAtLeast sample.codeA distance ∧
      HasMinimumDistanceAtLeast sample.codeB distance ∧
      HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
      HasMinimumDistanceAtLeast sample.codeB.dual distance)) :
    ∃ index : SimultaneousDistanceBadIndex r distance A B,
      simultaneousDistanceBad index sample := by
  by_cases hRank : sample.HasFullRowRank
  · by_cases hA : HasMinimumDistanceAtLeast sample.codeA distance
    · by_cases hB : HasMinimumDistanceAtLeast sample.codeB distance
      · by_cases hADual :
          HasMinimumDistanceAtLeast sample.codeA.dual distance
        · by_cases hBDual :
            HasMinimumDistanceAtLeast sample.codeB.dual distance
          · exact False.elim (hgood ⟨hRank, hA, hB, hADual, hBDual⟩)
          · have hSwapped :
                ¬HasMinimumDistanceAtLeast
                  (swapRandomLocalCodeSample r A B sample).codeA distance := by
              intro hDistance
              apply hBDual
              unfold HasMinimumDistanceAtLeast at hDistance ⊢
              intro word hword hwordNonzero
              apply hDistance word
              · have hCarrier :
                    sample.codeB.dual.carrier =
                      ((swapRandomLocalCodeSample r A B sample).codeA).carrier := by
                  change
                    (parityCheckKernelCode
                        (Matrix.toLin' sample.2)).dual.carrier =
                      (parityCheckRowCode
                        (Matrix.toLin' sample.2)).carrier
                  rw [← parityCheckRowCode_dual_eq_kernelCode]
                  exact dual_dual_carrier_eq _
                rw [← hCarrier]
                exact hword
              · exact hwordNonzero
            obtain ⟨index, hindex⟩ :=
              firstDistanceBad_covers_not_codeA_distance
                (swapRandomLocalCodeSample r A B sample) hSwapped
            exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr index))), hindex⟩
        · have hSwapped :
              ¬HasMinimumDistanceAtLeast
                (swapRandomLocalCodeSample r A B sample).codeB distance := by
            intro hDistance
            apply hADual
            unfold HasMinimumDistanceAtLeast at hDistance ⊢
            intro word hword hwordNonzero
            apply hDistance word
            · simpa [swapRandomLocalCodeSample,
                RandomLocalCodeSample.codeA,
                RandomLocalCodeSample.codeB,
                parityCheckRowCode_dual_eq_kernelCode] using hword
            · exact hwordNonzero
          obtain ⟨index, hindex⟩ :=
            secondDistanceBad_covers_not_codeB_distance
              (swapRandomLocalCodeSample r A B sample) hSwapped
          exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl index))), hindex⟩
      · obtain ⟨index, hindex⟩ :=
          secondDistanceBad_covers_not_codeB_distance sample hB
        exact ⟨Sum.inr (Sum.inr (Sum.inl index)), hindex⟩
    · obtain ⟨index, hindex⟩ :=
        firstDistanceBad_covers_not_codeA_distance sample hA
      exact ⟨Sum.inr (Sum.inl index), hindex⟩
  · obtain ⟨index, hindex⟩ :=
      rankDependencyBad_covers_not_fullRowRank sample hRank
    exact ⟨Sum.inl index, hindex⟩
private theorem sum_card_rankDependencyBad
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index : Bool ×
        {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0},
      (eventFinset (rankDependencyBad (A := A) (B := B) index)).card =
        2 * (2 ^ r - 1) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) := by
  have hEach : ∀ index : Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0},
      (eventFinset (rankDependencyBad (A := A) (B := B) index)).card =
        2 ^ (r * Delta - Delta) * 2 ^ (r * Delta) := by
    rintro ⟨side, ⟨coefficients, hcoefficients⟩⟩
    cases side
    · rw [eventFinset, ← Fintype.card_subtype]
      simp only [rankDependencyBad, Bool.false_eq_true, if_false]
      rw [Fintype.card_congr (firstRankDependencyEventEquiv coefficients)]
      rw [@Module.card_eq_pow_finrank (ZMod 2)
        (LinearMap.ker (fixedRowCombinationMap (col := A) coefficients) ×
          Matrix (ULift.{v} (Fin r)) B (ZMod 2)) _ _ _ _ _]
      have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      rw [hbase, Module.finrank_prod,
        finrank_ker_fixedRowCombinationMap hcoefficients,
        Module.finrank_matrix, pow_add]
      simp [hA, hB]
    · rw [eventFinset, ← Fintype.card_subtype]
      simp only [rankDependencyBad, if_true]
      rw [Fintype.card_congr (secondRankDependencyEventEquiv coefficients)]
      rw [@Module.card_eq_pow_finrank (ZMod 2)
        (Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
          LinearMap.ker (fixedRowCombinationMap (col := B) coefficients))
        _ _ _ _ _]
      have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
      rw [hbase, Module.finrank_prod, Module.finrank_matrix,
        finrank_ker_fixedRowCombinationMap hcoefficients, pow_add]
      simp [hA, hB, Nat.mul_comm]
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simpa using card_rankDependencyIndex (ULift.{v} (Fin r))
private theorem sum_card_simultaneousDistanceBad_le
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta) :
    ∑ index : SimultaneousDistanceBadIndex r distance A B,
      (eventFinset (simultaneousDistanceBad index)).card ≤
        2 * (2 ^ r - 1) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
          2 * (((2 ^ r - 1) *
              (∑ weight ∈ Finset.range distance,
                Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) *
            (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hRank := sum_card_rankDependencyBad (r := r) hA hB
  have hFirstA := sum_card_firstDistanceBad_le
    (r := r) (distance := distance) hA hB
  have hSecondB := sum_card_secondDistanceBad_le
    (r := r) (distance := distance) hA hB
  have hSecondA := sum_card_secondDistanceBad_le
    (r := r) (distance := distance) hB hA
  have hFirstB := sum_card_firstDistanceBad_le
    (r := r) (distance := distance) hB hA
  simp_rw [card_simultaneousDistanceBad_rank,
    card_simultaneousDistanceBad_first,
    card_simultaneousDistanceBad_second,
    card_simultaneousDistanceBad_firstDual,
    card_simultaneousDistanceBad_secondDual]
  omega
private theorem exists_eventual_simultaneousDistance_entropy_margins
    (rho delta : ℝ) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      Real.log 6 <
          ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) ∧
        Real.log 6 + Real.log 2 <
          (rho * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRhoLog : rho * Real.log 2 < (1 / 2 : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hRhoHalf hlog
  have hGeneratorSlope :
      0 < (1 - rho) * Real.log 2 - Real.binEntropy delta := by
    nlinarith [hEntropy, hRhoLog]
  have hKernelSlope :
      0 < rho * Real.log 2 - Real.binEntropy delta := by
    linarith
  obtain ⟨generatorThreshold, hGeneratorThreshold⟩ :=
    exists_nat_gt
      (Real.log 6 /
        ((1 - rho) * Real.log 2 - Real.binEntropy delta))
  obtain ⟨kernelThreshold, hKernelThreshold⟩ :=
    exists_nat_gt
      ((Real.log 6 + Real.log 2) /
        (rho * Real.log 2 - Real.binEntropy delta))
  refine ⟨max generatorThreshold kernelThreshold, ?_⟩
  intro Delta hThreshold
  have hGeneratorLe : generatorThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans hThreshold
  have hKernelLe : kernelThreshold ≤ Delta :=
    (Nat.le_max_right _ _).trans hThreshold
  have hGeneratorCast :
      (generatorThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hGeneratorLe
  have hKernelCast :
      (kernelThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hKernelLe
  have hGeneratorAtThreshold :
      Real.log 6 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
          (generatorThreshold : ℝ) := by
    have h := (div_lt_iff₀ hGeneratorSlope).mp hGeneratorThreshold
    nlinarith [h]
  have hKernelAtThreshold :
      Real.log 6 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) *
          (kernelThreshold : ℝ) := by
    have h := (div_lt_iff₀ hKernelSlope).mp hKernelThreshold
    nlinarith [h]
  constructor
  · have hScaled :=
      mul_le_mul_of_nonneg_left hGeneratorCast hGeneratorSlope.le
    nlinarith [hGeneratorAtThreshold, hScaled]
  · have hScaled :=
      mul_le_mul_of_nonneg_left hKernelCast hKernelSlope.le
    nlinarith [hKernelAtThreshold, hScaled]
private theorem exists_eventual_simultaneousDistance_parameters
    (rho delta : ℝ) (hRhoPositive : 0 < rho)
    (hRhoHalf : rho < 1 / 2) (hdeltaPositive : 0 < delta)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      0 < Delta ∧
        0 < randomRowCount rho Delta ∧
        randomRowCount rho Delta < Delta ∧
        2 ≤ Nat.ceil (delta * Delta) ∧
        Real.log 6 <
          ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) ∧
        Real.log 6 + Real.log 2 <
          (rho * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) := by
  obtain ⟨entropyThreshold, hEntropyThreshold⟩ :=
    exists_eventual_simultaneousDistance_entropy_margins
      rho delta hRhoHalf hEntropy
  obtain ⟨rowThreshold, hRowThreshold⟩ :=
    exists_nat_gt ((1 : ℝ) / rho)
  obtain ⟨radiusThreshold, hRadiusThreshold⟩ :=
    exists_nat_gt ((1 : ℝ) / delta)
  refine ⟨max entropyThreshold (max rowThreshold radiusThreshold), ?_⟩
  intro Delta hThreshold
  have hEntropyLe : entropyThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans hThreshold
  have hRowLe : rowThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans hThreshold)
  have hRadiusLe : radiusThreshold ≤ Delta :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans hThreshold)
  have hRowCast : (rowThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hRowLe
  have hRadiusCast : (radiusThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hRadiusLe
  have hRowAtThreshold : (1 : ℝ) < rho * rowThreshold := by
    have h := (div_lt_iff₀ hRhoPositive).mp hRowThreshold
    nlinarith [h]
  have hRadiusAtThreshold : (1 : ℝ) < delta * radiusThreshold := by
    have h := (div_lt_iff₀ hdeltaPositive).mp hRadiusThreshold
    nlinarith [h]
  have hRowLarge : (1 : ℝ) < rho * Delta := by
    have hScaled :=
      mul_le_mul_of_nonneg_left hRowCast hRhoPositive.le
    linarith
  have hRadiusLarge : (1 : ℝ) < delta * Delta := by
    have hScaled :=
      mul_le_mul_of_nonneg_left hRadiusCast hdeltaPositive.le
    linarith
  have hDeltaPositive : 0 < Delta := by
    by_contra h
    have hzero : Delta = 0 := by omega
    subst Delta
    norm_num at hRowLarge
  have hRowsPositive : 0 < randomRowCount rho Delta := by
    by_contra h
    have hzero : randomRowCount rho Delta = 0 := by omega
    have hfloor := randomRowCount_lt_add_one rho Delta
    rw [hzero] at hfloor
    norm_num at hfloor
    linarith
  have hRowsDegree : randomRowCount rho Delta < Delta :=
    randomRowCount_lt_degree hRhoPositive.le
      (by linarith : rho < 1) hDeltaPositive
  have hRadius : 2 ≤ Nat.ceil (delta * Delta) := by
    have hOne : 1 < Nat.ceil (delta * Delta) :=
      Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hRadiusLarge)
    omega
  obtain ⟨hGeneratorGap, hKernelGap⟩ :=
    hEntropyThreshold Delta hEntropyLe
  exact ⟨hDeltaPositive, hRowsPositive, hRowsDegree, hRadius,
    hGeneratorGap, hKernelGap⟩
private theorem hammingWeight_eq_sum_indicator_local
    {ι : Type v} [Fintype ι] (z : Word (ZMod 2) ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]
private theorem hammingWeight_eq_sum_columns
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) :
    HammingWeight x =
      ∑ b : B, HammingWeight (columnRestriction b x) := by
  classical
  calc
    HammingWeight x =
        ∑ coordinate : A × B, if x coordinate ≠ 0 then 1 else 0 :=
      hammingWeight_eq_sum_indicator_local x
    _ = ∑ a : A, ∑ b : B, if x (a, b) ≠ 0 then 1 else 0 :=
      Fintype.sum_prod_type _
    _ = ∑ b : B, ∑ a : A, if x (a, b) ≠ 0 then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ b : B, HammingWeight (columnRestriction b x) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hammingWeight_eq_sum_indicator_local]
      rfl
private theorem supportOverlap_eq_sum_indicator
    {ι : Type v} [Fintype ι] [DecidableEq ι] (x y : Word (ZMod 2) ι) :
    (hammingSupport x ∩ hammingSupport y).card =
      ∑ i, if x i ≠ 0 ∧ y i ≠ 0 then 1 else 0 := by
  have hSet : hammingSupport x ∩ hammingSupport y =
      Finset.univ.filter (fun i => x i ≠ 0 ∧ y i ≠ 0) := by
    ext i
    simp [hammingSupport]
  rw [hSet, Finset.card_filter]
private theorem hammingWeight_add_overlap_bound
    {ι : Type v} [Fintype ι] [DecidableEq ι] (x y : Word (ZMod 2) ι) :
    HammingWeight x + HammingWeight y ≤
      HammingWeight (x + y) + 2 * (hammingSupport x ∩ hammingSupport y).card := by
  rw [hammingWeight_eq_sum_indicator_local x,
    hammingWeight_eq_sum_indicator_local y,
    hammingWeight_eq_sum_indicator_local (x + y),
    supportOverlap_eq_sum_indicator]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x i = 0 <;> by_cases hy : y i = 0
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]
  · simp only [ne_eq, hx, hy, not_false_eq_true, and_self, ↓reduceIte, Pi.add_apply]
    omega
private theorem supportOverlap_eq_sum_columns
    {A B : Type v} [Fintype A] [Fintype B]
    (x y : Word (ZMod 2) (A × B)) :
    (hammingSupport x ∩ hammingSupport y).card =
      ∑ b : B, (hammingSupport (columnRestriction b x) ∩
        hammingSupport (columnRestriction b y)).card := by
  rw [supportOverlap_eq_sum_indicator]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [supportOverlap_eq_sum_indicator]
  rfl
private theorem supportOverlap_eq_sum_rows
    {A B : Type v} [Fintype A] [Fintype B]
    (x y : Word (ZMod 2) (A × B)) :
    (hammingSupport x ∩ hammingSupport y).card =
      ∑ a : A, (hammingSupport (rowRestriction a x) ∩
        hammingSupport (rowRestriction a y)).card := by
  rw [supportOverlap_eq_sum_indicator, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [supportOverlap_eq_sum_indicator]
  rfl
private theorem hammingWeight_eq_sum_rows
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) :
    HammingWeight x = ∑ a : A, HammingWeight (rowRestriction a x) := by
  rw [hammingWeight_eq_sum_indicator_local, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [hammingWeight_eq_sum_indicator_local]
  rfl
private theorem two_supportOverlap_le_columnPart_weight
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CA distance)
    (rowPart columnPart : Word (ZMod 2) (A × B))
    (hColumn : columnPart ∈ (columnCode (B := B) CA).carrier)
    (rows : Finset A) (hRows : 2 * rows.card ≤ distance)
    (hRowSupport : ∀ a, a ∉ rows → rowRestriction a rowPart = 0) :
    2 * (hammingSupport rowPart ∩ hammingSupport columnPart).card ≤
      HammingWeight columnPart := by
  rw [supportOverlap_eq_sum_columns, Finset.mul_sum, hammingWeight_eq_sum_columns]
  apply Finset.sum_le_sum
  intro b _
  by_cases hZero : columnRestriction b columnPart = 0
  · simp [hZero, hammingSupport, HammingWeight]
  · have hSubset : hammingSupport (columnRestriction b rowPart) ∩
        hammingSupport (columnRestriction b columnPart) ⊆ rows := by
      intro a ha
      by_contra hOutside
      have hNonzero := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
      exact hNonzero (congrFun (hRowSupport a hOutside) b)
    have hCard := Finset.card_le_card hSubset
    have hMin := hDistance _ (hColumn b) hZero
    omega
private theorem two_supportOverlap_le_rowPart_weight
    {A B : Type v} [Fintype A] [Fintype B]
    (CB : LinearCode (ZMod 2) B) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CB distance)
    (rowPart columnPart : Word (ZMod 2) (A × B))
    (hRow : rowPart ∈ (rowCode (A := A) CB).carrier)
    (columns : Finset B) (hColumns : 2 * columns.card ≤ distance)
    (hColumnSupport : ∀ b, b ∉ columns → columnRestriction b columnPart = 0) :
    2 * (hammingSupport rowPart ∩ hammingSupport columnPart).card ≤
      HammingWeight rowPart := by
  rw [supportOverlap_eq_sum_rows, Finset.mul_sum, hammingWeight_eq_sum_rows]
  apply Finset.sum_le_sum
  intro a _
  by_cases hZero : rowRestriction a rowPart = 0
  · simp [hZero, hammingSupport, HammingWeight]
  · have hSubset : hammingSupport (rowRestriction a rowPart) ∩
        hammingSupport (rowRestriction a columnPart) ⊆ columns := by
      intro b hb
      by_contra hOutside
      have hNonzero := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2
      exact hNonzero (congrFun (hColumnSupport b hOutside) a)
    have hCard := Finset.card_le_card hSubset
    have hMin := hDistance _ (hRow a) hZero
    omega
private theorem hammingWeight_parts_le_of_supported_decomposition
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (rowPart columnPart : Word (ZMod 2) (A × B))
    (hRow : rowPart ∈ (rowCode (A := A) CB).carrier)
    (hColumn : columnPart ∈ (columnCode (B := B) CA).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : 2 * rows.card ≤ distanceA)
    (hColumns : 2 * columns.card ≤ distanceB)
    (hRowSupport : ∀ a, a ∉ rows → rowRestriction a rowPart = 0)
    (hColumnSupport : ∀ b, b ∉ columns → columnRestriction b columnPart = 0) :
    HammingWeight rowPart ≤ HammingWeight (rowPart + columnPart) ∧
      HammingWeight columnPart ≤ HammingWeight (rowPart + columnPart) := by
  have hSum := hammingWeight_add_overlap_bound rowPart columnPart
  have hOverlapColumn := two_supportOverlap_le_columnPart_weight
    CA distanceA hDistanceA rowPart columnPart hColumn rows hRows hRowSupport
  have hOverlapRow := two_supportOverlap_le_rowPart_weight
    CB distanceB hDistanceB rowPart columnPart hRow columns hColumns hColumnSupport
  constructor <;> omega
private theorem heavyColumns_card_mul_succ_le_hammingWeight
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    ((Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x)).card) *
        (cutoff + 1) ≤ HammingWeight x := by
  classical
  let heavy : Finset B := Finset.univ.filter fun b =>
    cutoff < HammingWeight (columnRestriction b x)
  have hHeavy (b : B) (hb : b ∈ heavy) :
      cutoff + 1 ≤ HammingWeight (columnRestriction b x) := by
    simp only [heavy, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb
    omega
  change heavy.card * (cutoff + 1) ≤ HammingWeight x
  calc
    heavy.card * (cutoff + 1) = ∑ _b ∈ heavy, (cutoff + 1) := by
      simp [mul_comm]
    _ ≤ ∑ b ∈ heavy, HammingWeight (columnRestriction b x) := by
      apply Finset.sum_le_sum
      intro b hb
      exact hHeavy b hb
    _ ≤ ∑ b : B, HammingWeight (columnRestriction b x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro b _ _
      exact Nat.zero_le _
    _ = HammingWeight x := (hammingWeight_eq_sum_columns x).symm
private theorem heavyColumns_card_le_punctureBudget
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hWeight : HammingWeight x ≤ w)
    (hBudget : w < (p + 1) * (cutoff + 1)) :
    (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x)).card ≤ p := by
  have hHeavyWeight := heavyColumns_card_mul_succ_le_hammingWeight x cutoff
  by_contra h
  have hMany : p + 1 ≤
      (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)).card := by
    omega
  have hMul := Nat.mul_le_mul_right (cutoff + 1) hMany
  omega
private theorem supportCovered_lightRows_heavyColumns
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    SupportCovered x (lightRows x cutoff)
      (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)) := by
  classical
  intro coordinate hcoordinate
  obtain ⟨a, b⟩ := coordinate
  by_cases hb : b ∈ (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x))
  · apply Finset.mem_union.mpr
    right
    exact Finset.mem_product.mpr ⟨Finset.mem_univ a, hb⟩
  · have hx : x (a, b) ≠ 0 := by
      simpa [hammingSupport] using hcoordinate
    have hb' : ¬ cutoff < HammingWeight (columnRestriction b x) := by
      intro h
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩)
    have ha : a ∈ lightRows x cutoff := by
      simp only [lightRows, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b, hb', hx⟩
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_product.mpr ⟨ha, Finset.mem_univ b⟩
private theorem puncture_heavyColumns_has_many_lightRows
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hWeight : HammingWeight x ≤ w)
    (hBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p →
        ¬ SupportCovered x rows columns) :
    p < (lightRows x cutoff).card := by
  have hHeavy := heavyColumns_card_le_punctureBudget x cutoff w p
    hWeight hBudget
  by_contra h
  have hRows : (lightRows x cutoff).card ≤ p := by omega
  exact hNoCover (lightRows x cutoff)
    (Finset.univ.filter fun b : B =>
      cutoff < HammingWeight (columnRestriction b x))
    hRows hHeavy (supportCovered_lightRows_heavyColumns x cutoff)
private theorem card_lowWeightColumnMatrices
    (A B : Type v) [Fintype A] [Fintype B] [DecidableEq A]
    (distance : Nat) :
    Fintype.card {x : Word (ZMod 2) (A × B) //
      ∀ b : B, HammingWeight (columnRestriction b x) < distance} =
      (∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  rw [Fintype.card_congr (lowWeightColumnMatricesEquiv A B distance),
    Fintype.card_fun, card_binaryLowWeightWords]
private theorem card_keptCoordinate
    (B : Type v) [Fintype B] (removed : Finset B) :
    Fintype.card (KeptCoordinate removed) =
      Fintype.card B - removed.card := by
  classical
  rw [Fintype.card_subtype_compl (fun b : B => b ∈ removed)]
  simp [Fintype.card_subtype]
private theorem hammingSupport_subset_biUnion_of_mem_span
    {ι : Type v} [Fintype ι]
    (columns : Finset (Word (ZMod 2) ι))
    {x : Word (ZMod 2) ι}
    (hx : x ∈ Submodule.span (ZMod 2) (columns : Set (Word (ZMod 2) ι))) :
    hammingSupport x ⊆ columns.biUnion hammingSupport := by
  classical
  intro coordinate hcoordinate
  by_contra hmissing
  let evaluate : Word (ZMod 2) ι →ₗ[ZMod 2] ZMod 2 := {
    toFun := fun word => word coordinate
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hspan :
      Submodule.span (ZMod 2) (columns : Set (Word (ZMod 2) ι)) ≤
        LinearMap.ker evaluate := by
    apply Submodule.span_le.mpr
    intro word hword
    change word coordinate = 0
    by_contra hnonzero
    apply hmissing
    exact Finset.mem_biUnion.mpr
      ⟨word, hword, by simpa [hammingSupport] using hnonzero⟩
  have hzero : x coordinate = 0 := by
    have hkernel := hspan hx
    change evaluate x = 0 at hkernel
    exact hkernel
  have hnonzero : x coordinate ≠ 0 := by
    simpa [hammingSupport] using hcoordinate
  exact hnonzero hzero
private theorem card_biUnion_hammingSupport_le_finrank_mul
    {ι : Type v} [Fintype ι]
    (columns : Finset (Word (ZMod 2) ι)) (cutoff : Nat)
    (hLight : ∀ word ∈ columns, HammingWeight word ≤ cutoff) :
    (columns.biUnion hammingSupport).card ≤
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) * cutoff := by
  classical
  obtain ⟨basis, hsubset, hcard, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn
      (ZMod 2) (columns : Set (Word (ZMod 2) ι))
  have hcover : columns.biUnion hammingSupport ⊆
      basis.biUnion hammingSupport := by
    intro coordinate hcoordinate
    obtain ⟨word, hword, hsupport⟩ := Finset.mem_biUnion.mp hcoordinate
    have hmem : word ∈ Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι)) :=
      Submodule.subset_span hword
    rw [← hspan] at hmem
    exact hammingSupport_subset_biUnion_of_mem_span basis hmem hsupport
  calc
    (columns.biUnion hammingSupport).card ≤
        (basis.biUnion hammingSupport).card := Finset.card_le_card hcover
    _ ≤ basis.card * cutoff := by
      apply Finset.card_biUnion_le_card_mul
      intro word hword
      simpa [HammingWeight_eq_card_hammingSupport] using
        hLight word (hsubset hword)
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) * cutoff := by
      rw [hcard]
private theorem lightRows_eq_biUnion_lightColumns
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    lightRows x cutoff =
      ((Finset.univ.filter fun b : B =>
        HammingWeight (columnRestriction b x) ≤ cutoff).image
          (fun b => columnRestriction b x)).biUnion hammingSupport := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hx⟩ := by
      simpa only [lightRows, Finset.mem_filter, Finset.mem_univ,
        true_and] using ha
    have hLight : HammingWeight (columnRestriction b x) ≤ cutoff :=
      Nat.le_of_not_gt hb
    apply Finset.mem_biUnion.mpr
    refine ⟨columnRestriction b x, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨b, Finset.mem_filter.mpr
        ⟨Finset.mem_univ b, hLight⟩, rfl⟩
    · change a ∈ (Finset.univ.filter fun i : A =>
        (columnRestriction b x) i ≠ 0)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hx⟩
  · intro ha
    obtain ⟨word, hword, hsupport⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
    have hLight := (Finset.mem_filter.mp hb).2
    have hNotHeavy : b ∉ (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)) := by
      intro hHeavy
      have hGreater := (Finset.mem_filter.mp hHeavy).2
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ a, ⟨b, hNotHeavy, ?_⟩⟩
    change a ∈ (Finset.univ.filter fun i : A =>
      (columnRestriction b x) i ≠ 0) at hsupport
    exact (Finset.mem_filter.mp hsupport).2
private theorem lightRows_card_le_lightColumnSpan_finrank_mul
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    (lightRows x cutoff).card ≤
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (((Finset.univ.filter fun b : B =>
            HammingWeight (columnRestriction b x) ≤ cutoff).image
              (fun b => columnRestriction b x)) :
                Set (Word (ZMod 2) A))) * cutoff := by
  classical
  rw [lightRows_eq_biUnion_lightColumns]
  apply card_biUnion_hammingSupport_le_finrank_mul
  intro word hword
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
  exact (Finset.mem_filter.mp hb).2
private theorem puncture_lightColumnSpan_rank_mul_gt_budget
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hWeight : HammingWeight x ≤ w)
    (hBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p →
        ¬ SupportCovered x rows columns) :
    p < Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (((Finset.univ.filter fun b : B =>
          HammingWeight (columnRestriction b x) ≤ cutoff).image
            (fun b => columnRestriction b x)) :
              Set (Word (ZMod 2) A))) * cutoff :=
  (puncture_heavyColumns_has_many_lightRows x cutoff w p
    hWeight hBudget hNoCover).trans_le
      (lightRows_card_le_lightColumnSpan_finrank_mul x cutoff)
private theorem syndrome_injective_on_smallSupport_span
    {ι M : Type v} [Fintype ι] [AddCommGroup M] [Module (ZMod 2) M]
    (syndrome : Word (ZMod 2) ι →ₗ[ZMod 2] M)
    (columns : Finset (Word (ZMod 2) ι)) (distance : Nat)
    (hDistance : ∀ word, syndrome word = 0 → word ≠ 0 →
      distance ≤ HammingWeight word)
    (hSupport : (columns.biUnion hammingSupport).card < distance)
    {word : Word (ZMod 2) ι}
    (hWord : word ∈ Submodule.span (ZMod 2)
      (columns : Set (Word (ZMod 2) ι)))
    (hSyndrome : syndrome word = 0) : word = 0 := by
  classical
  by_contra hNonzero
  have hSubset := hammingSupport_subset_biUnion_of_mem_span columns hWord
  have hWeight : HammingWeight word ≤
      (columns.biUnion hammingSupport).card := by
    simpa [HammingWeight_eq_card_hammingSupport] using
      (Finset.card_le_card hSubset)
  have hMin := hDistance word hSyndrome hNonzero
  omega
private theorem syndrome_smallSupport_span_finrank_eq
    {ι M : Type v} [Fintype ι] [AddCommGroup M] [Module (ZMod 2) M]
    (syndrome : Word (ZMod 2) ι →ₗ[ZMod 2] M)
    (columns : Finset (Word (ZMod 2) ι)) (distance : Nat)
    (hDistance : ∀ word, syndrome word = 0 → word ≠ 0 →
      distance ≤ HammingWeight word)
    (hSupport : (columns.biUnion hammingSupport).card < distance) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map syndrome) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) := by
  classical
  let span := Submodule.span (ZMod 2)
    (columns : Set (Word (ZMod 2) ι))
  have hinjective : Function.Injective (syndrome.domRestrict span) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply syndrome_injective_on_smallSupport_span syndrome columns distance
      hDistance hSupport
    · exact span.sub_mem x.property y.property
    · have heq : syndrome (x : Word (ZMod 2) ι) =
          syndrome (y : Word (ZMod 2) ι) := hxy
      simpa only [map_sub, sub_eq_zero] using heq
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinjective
private theorem codeQuotient_smallSupport_span_finrank_eq
    {ι : Type v} [Fintype ι]
    (code : LinearCode (ZMod 2) ι)
    (columns : Finset (Word (ZMod 2) ι)) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast code distance)
    (hSupport : (columns.biUnion hammingSupport).card < distance) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))) := by
  apply syndrome_smallSupport_span_finrank_eq code.carrier.mkQ columns distance
  · intro word hKernel hNonzero
    exact hDistance word
      ((Submodule.Quotient.mk_eq_zero code.carrier).mp hKernel) hNonzero
  · exact hSupport
private theorem codeQuotient_lightIndependent_finrank_le
    {ι : Type v} [Fintype ι]
    (code : LinearCode (ZMod 2) ι)
    (columns basis : Finset (Word (ZMod 2) ι))
    (cutoff distance : Nat)
    (hBasis : basis ⊆ columns)
    (hIndependent : LinearIndepOn (ZMod 2) id
      (basis : Set (Word (ZMod 2) ι)))
    (hLight : ∀ word ∈ basis, HammingWeight word ≤ cutoff)
    (hCount : basis.card * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    basis.card ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) := by
  classical
  have hSupport : (basis.biUnion hammingSupport).card < distance := by
    apply lt_of_le_of_lt _ hCount
    apply Finset.card_biUnion_le_card_mul
    intro word hword
    simpa [HammingWeight_eq_card_hammingSupport] using hLight word hword
  have hRank := codeQuotient_smallSupport_span_finrank_eq
    code basis distance hDistance hSupport
  calc
    basis.card = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (basis : Set (Word (ZMod 2) ι))) :=
      (finrank_span_finset_eq_card hIndependent).symm
    _ = Module.finrank (ZMod 2)
        ((Submodule.span (ZMod 2)
          (basis : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) :=
      hRank.symm
    _ ≤ Module.finrank (ZMod 2)
        ((Submodule.span (ZMod 2)
          (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) :=
      Submodule.finrank_mono
        (Submodule.map_mono (Submodule.span_mono hBasis))
private theorem codeQuotient_lightColumns_rank_le
    {ι : Type v} [Fintype ι]
    (code : LinearCode (ZMod 2) ι)
    (columns : Finset (Word (ZMod 2) ι))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))))
    (hLight : ∀ word ∈ columns, HammingWeight word ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    rank ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        (columns : Set (Word (ZMod 2) ι))).map code.carrier.mkQ) := by
  classical
  obtain ⟨basis, hbasis, hcard, _, hindependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn
      (ZMod 2) (columns : Set (Word (ZMod 2) ι))
  obtain ⟨chosen, hChosenBasis, hChosenCard⟩ :=
    Finset.exists_subset_card_eq (hcard.symm ▸ hRank)
  have hChosenColumns : chosen ⊆ columns := by
    intro word hword
    exact hbasis (hChosenBasis hword)
  have hChosenIndependent : LinearIndepOn (ZMod 2) id
      (chosen : Set (Word (ZMod 2) ι)) := by
    apply hindependent.mono
    intro word hword
    exact hChosenBasis hword
  have hChosenLight : ∀ word ∈ chosen,
      HammingWeight word ≤ cutoff := by
    intro word hword
    exact hLight word (hChosenColumns hword)
  have hChosenBudget : chosen.card * cutoff < distance := by
    simpa only [hChosenCard] using hBudget
  simpa only [hChosenCard] using
    (codeQuotient_lightIndependent_finrank_le code columns chosen
      cutoff distance hChosenColumns hChosenIndependent hChosenLight
      hChosenBudget hDistance)
private theorem quotientCheckRestriction_surjective
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row)) :
    Function.Surjective (quotientCheckRestriction testSpace deletedSyndromes) := by
  intro prescribed
  obtain ⟨lifted, hLifted⟩ :=
    deletedSyndromes.mkQ_surjective.surjective_linearMapComp_left prescribed
  obtain ⟨check, hCheck⟩ := lifted.exists_extend
  refine ⟨Matrix.toLin'.symm check, ?_⟩
  change (deletedSyndromes.mkQ.comp
    (Matrix.toLin' (Matrix.toLin'.symm check))).comp testSpace.subtype = prescribed
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_assoc, hCheck]
  exact hLifted
private theorem card_ker_quotientCheckRestriction_mul_pow
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row)) :
    Fintype.card (LinearMap.ker
      (quotientCheckRestriction testSpace deletedSyndromes)) *
        2 ^ (Module.finrank (ZMod 2) testSpace *
          (Fintype.card row - Module.finrank (ZMod 2) deletedSyndromes)) =
      Fintype.card (Matrix row col (ZMod 2)) := by
  classical
  let f := quotientCheckRestriction testSpace deletedSyndromes
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr
      (quotientCheckRestriction_surjective testSpace deletedSyndromes)
  have hRankNullity := f.finrank_range_add_finrank_ker
  rw [hRange, finrank_top, Module.finrank_linearMap,
    Submodule.finrank_quotient, finrank_word_eq_length] at hRankNullity
  norm_num [Length, Module.finrank_matrix] at hRankNullity
  rw [@Module.card_eq_pow_finrank (ZMod 2) (LinearMap.ker f)
    _ _ _ _ _, card_binaryMatrix]
  have hbase : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hbase, ← pow_add]
  congr 1
  simpa only [Nat.add_comm] using hRankNullity
private theorem card_ker_quotientCheckRestriction_mul_pow_le
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row))
    (p : Nat) (hDeleted : Module.finrank (ZMod 2) deletedSyndromes ≤ p) :
    Fintype.card (LinearMap.ker
      (quotientCheckRestriction testSpace deletedSyndromes)) *
        2 ^ (Module.finrank (ZMod 2) testSpace * (Fintype.card row - p)) ≤
      Fintype.card (Matrix row col (ZMod 2)) := by
  calc
    _ ≤ Fintype.card (LinearMap.ker
        (quotientCheckRestriction testSpace deletedSyndromes)) *
          2 ^ (Module.finrank (ZMod 2) testSpace *
            (Fintype.card row - Module.finrank (ZMod 2) deletedSyndromes)) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega : 0 < 2)
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hDeleted _)
    _ = _ := card_ker_quotientCheckRestriction_mul_pow testSpace deletedSyndromes
private theorem card_splitPunctureCheckEvent_mul_pow_le
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) kept)) :
    Fintype.card {sample : Matrix row deleted (ZMod 2) ×
        Matrix row kept (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} *
      2 ^ (Module.finrank (ZMod 2) testSpace *
        (Fintype.card row - Fintype.card deleted)) ≤
      Fintype.card (Matrix row deleted (ZMod 2) ×
        Matrix row kept (ZMod 2)) := by
  classical
  rw [Fintype.card_congr (splitPunctureCheckEventEquiv testSpace),
    Fintype.card_sigma, Finset.sum_mul, Fintype.card_prod]
  calc
    _ ≤ ∑ _deletedMatrix : Matrix row deleted (ZMod 2),
        Fintype.card (Matrix row kept (ZMod 2)) := by
      apply Finset.sum_le_sum
      intro deletedMatrix _
      apply card_ker_quotientCheckRestriction_mul_pow_le
      simpa only [finrank_word_eq_length, Length] using
        (Matrix.toLin' deletedMatrix).finrank_range_le
    _ = _ := by simp
private theorem card_mul_le_of_equivs
    {α β γ δ : Type*}
    (events : α ≃ β) (samples : γ ≃ δ) (factor scale : Nat)
    (hFactor : factor = scale)
    (h : Nat.card β * factor ≤ Nat.card δ) :
    Nat.card α * scale ≤ Nat.card γ := by
  subst scale
  rw [Nat.card_congr events, Nat.card_congr samples]
  exact h
private theorem nat_card_splitPunctureCheckEvent_mul_pow_le
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) kept)) :
    Nat.card {sample : Matrix row deleted (ZMod 2) × Matrix row kept (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} *
      2 ^ (Module.finrank (ZMod 2) testSpace *
        (Fintype.card row - Fintype.card deleted)) ≤
      Nat.card (Matrix row deleted (ZMod 2) × Matrix row kept (ZMod 2)) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact card_splitPunctureCheckEvent_mul_pow_le testSpace
private theorem card_puncturedCheckMatrixEvent_mul_pow_le
    {row col : Type v} [Fintype row] [Fintype col]
    (removed : Finset col)
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) (KeptCoordinate removed))) :
    Nat.card {matrix : Matrix row col (ZMod 2) // ∀ word : testSpace,
      word.1 ∈ (puncturedCode
        (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} *
      2 ^ (Module.finrank (ZMod 2) testSpace *
        (Fintype.card row - removed.card)) ≤
      Nat.card (Matrix row col (ZMod 2)) := by
  have hDeleted : Fintype.card {i : col // i ∈ removed} = removed.card :=
    Fintype.card_coe removed
  have hFactor := congrArg
    (fun p => 2 ^ (Module.finrank (ZMod 2) testSpace * (Fintype.card row - p))) hDeleted
  exact card_mul_le_of_equivs
    (puncturedCheckMatrixEventEquiv removed testSpace)
    (splitCheckMatrixEquiv (row := row) removed) _ _ hFactor
    (nat_card_splitPunctureCheckEvent_mul_pow_le
      (row := row) (deleted := {i : col // i ∈ removed})
      (kept := KeptCoordinate removed) testSpace)
private theorem hammingWeight_le_of_mem_supportedWordSpace
    {A : Type v} [Fintype A] (support : Finset A)
    {word : Word (ZMod 2) A} (hWord : word ∈ supportedWordSpace support) :
    HammingWeight word ≤ support.card := by
  apply Finset.card_le_card
  intro a ha
  by_contra hOutside
  exact (Finset.mem_filter.mp ha).2 (hWord a hOutside)
private theorem check_supportedWordSpace_ker_eq_bot
    {A M : Type v} [Fintype A] [AddCommGroup M] [Module (ZMod 2) M]
    (check : Word (ZMod 2) A →ₗ[ZMod 2] M)
    (support : Finset A) (distance : Nat)
    (hDistance : ∀ word, check word = 0 → word ≠ 0 →
      distance ≤ HammingWeight word)
    (hSupport : support.card < distance) :
    LinearMap.ker (check.domRestrict (supportedWordSpace support)) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hNonzero
  have hZero : check ((x : Word (ZMod 2) A) - y) = 0 := by
    change check (x : Word (ZMod 2) A) = check (y : Word (ZMod 2) A) at hxy
    simpa only [map_sub, sub_eq_zero] using hxy
  have hWeight := hammingWeight_le_of_mem_supportedWordSpace support
    ((supportedWordSpace support).sub_mem x.property y.property)
  have hMin := hDistance _ hZero hNonzero
  omega
private theorem exists_supportedWordRecovery
    {A M : Type v} [Fintype A] [AddCommGroup M] [Module (ZMod 2) M]
    (check : Word (ZMod 2) A →ₗ[ZMod 2] M)
    (support : Finset A)
    (hInjective : LinearMap.ker
      (check.domRestrict (supportedWordSpace support)) = ⊥) :
    ∃ recovery : M →ₗ[ZMod 2] Word (ZMod 2) A,
      LinearMap.range recovery ≤ supportedWordSpace support ∧
      (∀ word ∈ supportedWordSpace support, recovery (check word) = word) ∧
      (∀ syndrome ∈ (supportedWordSpace support).map check,
        check (recovery syndrome) = syndrome) := by
  let space := supportedWordSpace support
  obtain ⟨inverse, hInverse⟩ :=
    (check.domRestrict space).exists_leftInverse_of_injective hInjective
  let recovery := space.subtype.comp inverse
  have hRecover : ∀ word ∈ space, recovery (check word) = word := by
    intro word hWord
    exact congrArg Subtype.val (LinearMap.congr_fun hInverse ⟨word, hWord⟩)
  refine ⟨recovery, ?_, hRecover, ?_⟩
  · rintro _ ⟨syndrome, rfl⟩
    exact (inverse syndrome).property
  · intro syndrome hSyndrome
    obtain ⟨word, hWord, rfl⟩ := hSyndrome
    rw [hRecover word hWord]
private theorem exists_squareParityCheckMatrix_ker_eq
    {A : Type v} [Fintype A]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A)) :
    ∃ check : Matrix A A (ZMod 2), LinearMap.ker (Matrix.toLin' check) = code := by
  obtain ⟨complement, hComplement⟩ := code.exists_isCompl
  refine ⟨LinearMap.toMatrix' (complement.projection code hComplement.symm), ?_⟩
  rw [Matrix.toLin'_toMatrix']
  exact Submodule.ker_projection hComplement.symm
private theorem check_map_finrank_eq_quotient
    {A R : Type v} [Fintype A] [Fintype R]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A))
    (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code)
    (space : Submodule (ZMod 2) (Word (ZMod 2) A)) :
    Module.finrank (ZMod 2) (space.map (Matrix.toLin' check)) =
      Module.finrank (ZMod 2) (space.map code.mkQ) := by
  let lifted := code.liftQ (Matrix.toLin' check) hKernel.symm.le
  have hInjective : Function.Injective lifted :=
    LinearMap.ker_eq_bot.mp
      (code.ker_liftQ_eq_bot (Matrix.toLin' check) hKernel.symm.le hKernel.le)
  calc
    Module.finrank (ZMod 2) (space.map (Matrix.toLin' check)) =
        Module.finrank (ZMod 2) ((space.map code.mkQ).map lifted) := by
      rw [← Submodule.map_comp, Submodule.liftQ_mkQ]
    _ = Module.finrank (ZMod 2) (space.map code.mkQ) := by
      rw [← LinearMap.range_domRestrict]
      apply LinearMap.finrank_range_of_inj
      exact hInjective.comp Subtype.val_injective
private theorem syndrome_columnSpan_finrank_eq_rowSpan
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (check : Matrix R A (ZMod 2)) (x : Word (ZMod 2) (A × B)) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2) (Set.range fun b : B =>
        columnRestriction b x)).map (Matrix.toLin' check)) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun r : R =>
          (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  let syndrome : Matrix R B (ZMod 2) :=
    fun r b => Matrix.mulVec check (columnRestriction b x) r
  have hSpace :
      (Submodule.span (ZMod 2) (Set.range fun b : B =>
        columnRestriction b x)).map (Matrix.toLin' check) =
      Submodule.span (ZMod 2) (Set.range syndrome.col) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hSpace, ← syndrome.rank_eq_finrank_span_cols,
    syndrome.rank_eq_finrank_span_row]
  rfl
private theorem check_columnQuotient_finrank_eq_rowSpan
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A))
    (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code)
    (x : Word (ZMod 2) (A × B)) :
    Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2) (Set.range fun b : B =>
        columnRestriction b x)).map code.mkQ) =
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun r : R =>
          (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  rw [← check_map_finrank_eq_quotient code check hKernel]
  exact syndrome_columnSpan_finrank_eq_rowSpan check x
private theorem check_columnQuotient_rank_le_rowSpan
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (code : Submodule (ZMod 2) (Word (ZMod 2) A))
    (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code)
    (x : Word (ZMod 2) (A × B)) (rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      ((Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : B => columnRestriction b x) :
          Set (Word (ZMod 2) A))).map code.mkQ)) :
    rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun r : R =>
        (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  have hColumns :
      ((Finset.univ.image fun b : B => columnRestriction b x) :
        Set (Word (ZMod 2) A)) =
      Set.range (fun b : B => columnRestriction b x) := by
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hColumns, check_columnQuotient_finrank_eq_rowSpan code check hKernel x] at hRank
  exact hRank
private theorem check_lightColumns_rowSpan_rank_le
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (code : LinearCode (ZMod 2) A) (check : Matrix R A (ZMod 2))
    (hKernel : LinearMap.ker (Matrix.toLin' check) = code.carrier)
    (x : Word (ZMod 2) (A × B)) (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : B => columnRestriction b x) :
          Set (Word (ZMod 2) A))))
    (hLight : ∀ b : B, HammingWeight (columnRestriction b x) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun r : R =>
        (fun b => Matrix.mulVec check (columnRestriction b x) r))) := by
  apply check_columnQuotient_rank_le_rowSpan code.carrier check hKernel x rank
  apply codeQuotient_lightColumns_rank_le code _ cutoff distance rank hRank
  · intro word hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    exact hLight b
  · exact hBudget
  · exact hDistance
private theorem syndrome_row_mem_of_mem_dualTensorCode
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (check : Matrix R A (ZMod 2))
    (hCheck : CA.carrier ≤ LinearMap.ker (Matrix.toLin' check))
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) (r : R) :
    (fun b => Matrix.mulVec check (columnRestriction b x) r) ∈ CB.carrier := by
  obtain ⟨columnPart, hColumn, rowPart, hRow, hParts⟩ := Submodule.mem_sup.mp hx
  have hZero : ∀ b, Matrix.mulVec check (columnRestriction b columnPart) = 0 := by
    intro b
    exact hCheck (hColumn b)
  have hRows :
      (fun b => Matrix.mulVec check (columnRestriction b x) r) =
        ∑ a : A, check r a • rowRestriction a rowPart := by
    funext b
    rw [← hParts, map_add, Matrix.mulVec_add, hZero, zero_add]
    simp [Matrix.mulVec, dotProduct, rowRestriction, columnRestriction]
  rw [hRows]
  exact CB.carrier.sum_mem fun a _ => CB.carrier.smul_mem (check r a) (hRow a)
private theorem column_mem_supportedWordSpace_of_supportCovered
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (rows : Finset A) (columns : Finset B)
    (hCovered : SupportCovered x rows columns) (b : B) (hb : b ∉ columns) :
    columnRestriction b x ∈ supportedWordSpace rows := by
  intro a ha
  by_contra hNonzero
  have hMem := hCovered (by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNonzero⟩)
  rcases Finset.mem_union.mp hMem with hRow | hColumn
  · exact ha (Finset.mem_product.mp hRow).1
  · exact hb (Finset.mem_product.mp hColumn).2
private theorem linearMap_row_mem_of_mem_dualTensorCode
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (check : Word (ZMod 2) A →ₗ[ZMod 2] Word (ZMod 2) R)
    (hCheck : CA.carrier ≤ LinearMap.ker check)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) (r : R) :
    (fun b => check (columnRestriction b x) r) ∈ CB.carrier := by
  have hMatrix : CA.carrier ≤
      LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix' check)) := by
    simpa only [Matrix.toLin'_toMatrix'] using hCheck
  have hRow := syndrome_row_mem_of_mem_dualTensorCode CA CB
    (LinearMap.toMatrix' check) hMatrix x hx r
  change (fun b => Matrix.toLin' (LinearMap.toMatrix' check)
    (columnRestriction b x) r) ∈ CB.carrier at hRow
  simpa only [Matrix.toLin'_toMatrix'] using hRow
private theorem exists_supported_dualTensor_decomposition
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < distanceA) (hColumns : columns.card < distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      (∀ a, a ∉ rows → rowRestriction a rowPart = 0) ∧
      (∀ b, b ∉ columns → columnRestriction b columnPart = 0) := by
  obtain ⟨matrix, hKernel⟩ := exists_squareParityCheckMatrix_ker_eq CA.carrier
  let check := Matrix.toLin' matrix
  have hCheckDistance : ∀ word, check word = 0 → word ≠ 0 →
      distanceA ≤ HammingWeight word := by
    intro word hZero hNonzero
    apply hDistanceA word _ hNonzero
    rw [← hKernel]
    exact hZero
  obtain ⟨recovery, hRecoveryRange, hRecover, _⟩ :=
    exists_supportedWordRecovery check rows
      (check_supportedWordSpace_ker_eq_bot check rows distanceA hCheckDistance hRows)
  let corrector := recovery.comp check
  let obstruction := check - check.comp corrector
  have hCheckZero : ∀ word ∈ CA.carrier, check word = 0 := by
    intro word hWord
    have h := hWord
    rw [← hKernel] at h
    exact h
  have hCorrectorKernel : CA.carrier ≤ LinearMap.ker corrector := by
    intro word hWord
    change recovery (check word) = 0
    rw [hCheckZero word hWord, map_zero]
  have hObstructionKernel : CA.carrier ≤ LinearMap.ker obstruction := by
    intro word hWord
    change check word - check (corrector word) = 0
    rw [hCheckZero word hWord, hCorrectorKernel hWord, map_zero, sub_self]
  have hOutside : ∀ b, b ∉ columns →
      columnRestriction b x ∈ supportedWordSpace rows := by
    intro b hb
    exact column_mem_supportedWordSpace_of_supportCovered x rows columns hCovered b hb
  have hObstructionOutside : ∀ b, b ∉ columns →
      obstruction (columnRestriction b x) = 0 := by
    intro b hb
    change check (columnRestriction b x) -
      check (recovery (check (columnRestriction b x))) = 0
    rw [hRecover _ (hOutside b hb), sub_self]
  have hObstructionRowZero : ∀ a : A,
      (fun b => obstruction (columnRestriction b x) a) = 0 := by
    intro a
    have hRow := linearMap_row_mem_of_mem_dualTensorCode CA CB
      obstruction hObstructionKernel x hx a
    have hSupport : (fun b => obstruction (columnRestriction b x) a) ∈
        supportedWordSpace columns := by
      intro b hb
      exact congrFun (hObstructionOutside b hb) a
    have hWeight := hammingWeight_le_of_mem_supportedWordSpace columns hSupport
    by_contra hNonzero
    have hMin := hDistanceB _ hRow hNonzero
    omega
  have hCheckCorrect : ∀ b, check (corrector (columnRestriction b x)) =
      check (columnRestriction b x) := by
    intro b
    have hZero : obstruction (columnRestriction b x) = 0 := by
      funext a
      exact congrFun (hObstructionRowZero a) b
    exact (sub_eq_zero.mp hZero).symm
  let rowPart : Word (ZMod 2) (A × B) :=
    fun ab => corrector (columnRestriction ab.2 x) ab.1
  let columnPart := x - rowPart
  have hRowPart : rowPart ∈ (rowCode (A := A) CB).carrier := by
    intro a
    exact linearMap_row_mem_of_mem_dualTensorCode CA CB
      corrector hCorrectorKernel x hx a
  have hColumnPart : columnPart ∈ (columnCode (B := B) CA).carrier := by
    intro b
    rw [← hKernel]
    change check (columnRestriction b x - corrector (columnRestriction b x)) = 0
    rw [map_sub, hCheckCorrect b, sub_self]
  refine ⟨rowPart, columnPart, hRowPart, hColumnPart, ?_, ?_, ?_⟩
  · exact (sub_add_cancel x rowPart).symm.trans (add_comm _ _)
  · intro a ha
    funext b
    have hSupport := hRecoveryRange
      (LinearMap.mem_range.mpr ⟨check (columnRestriction b x), rfl⟩)
    exact hSupport a ha
  · intro b hb
    funext a
    change x (a, b) - recovery (check (columnRestriction b x)) a = 0
    rw [hRecover _ (hOutside b hb)]
    exact sub_self _
private theorem activeRowSet_card_mul_distance_le
    {A B : Type v} [Fintype A] [Fintype B]
    (CB : LinearCode (ZMod 2) B) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CB distance)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (rowCode (A := A) CB).carrier) :
    (activeRowSet x).card * distance ≤ HammingWeight x := by
  rw [activeRowSet, Finset.card_filter, Finset.sum_mul, hammingWeight_eq_sum_rows]
  apply Finset.sum_le_sum
  intro a _
  by_cases hZero : rowRestriction a x = 0
  · simp [hZero]
  · simpa [hZero] using hDistance _ (hx a) hZero
private theorem activeColumnSet_card_mul_distance_le
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (distance : Nat)
    (hDistance : HasMinimumDistanceAtLeast CA distance)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (columnCode (B := B) CA).carrier) :
    (activeColumnSet x).card * distance ≤ HammingWeight x := by
  rw [activeColumnSet, Finset.card_filter, Finset.sum_mul, hammingWeight_eq_sum_columns]
  apply Finset.sum_le_sum
  intro b _
  by_cases hZero : columnRestriction b x = 0
  · simp [hZero]
  · simpa [hZero] using hDistance _ (hx b) hZero
private theorem supportCovered_add_activeParts
    {A B : Type v} [Fintype A] [Fintype B]
    (rowPart columnPart : Word (ZMod 2) (A × B)) :
    SupportCovered (rowPart + columnPart)
      (activeRowSet rowPart) (activeColumnSet columnPart) := by
  intro ab hMem
  by_cases hRow : rowRestriction ab.1 rowPart = 0
  · have hRowZero : rowPart ab = 0 := congrFun hRow ab.2
    have hColumn : columnRestriction ab.2 columnPart ≠ 0 := by
      intro hZero
      have hColumnZero : columnPart ab = 0 := congrFun hZero ab.1
      exact (Finset.mem_filter.mp hMem).2
        (by simp [Pi.add_apply, hRowZero, hColumnZero])
    apply Finset.mem_union.mpr
    right
    simp [Finset.mem_product, activeColumnSet, hColumn]
  · apply Finset.mem_union.mpr
    left
    simp [Finset.mem_product, activeRowSet, hRow]
private theorem exists_distanceNormalized_supportCover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hPositiveA : 0 < distanceA) (hPositiveB : 0 < distanceB)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : 2 * rows.card ≤ distanceA)
    (hColumns : 2 * columns.card ≤ distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ normalizedRows : Finset A, ∃ normalizedColumns : Finset B,
      SupportCovered x normalizedRows normalizedColumns ∧
        normalizedRows.card ≤ HammingWeight x / distanceB ∧
        normalizedColumns.card ≤ HammingWeight x / distanceA := by
  obtain ⟨rowPart, columnPart, hRow, hColumn, hParts, hRowSupport, hColumnSupport⟩ :=
    exists_supported_dualTensor_decomposition CA CB distanceA distanceB
      hDistanceA hDistanceB x hx rows columns (by omega) (by omega) hCovered
  have hWeights := hammingWeight_parts_le_of_supported_decomposition
    CA CB distanceA distanceB hDistanceA hDistanceB rowPart columnPart
      hRow hColumn rows columns hRows hColumns hRowSupport hColumnSupport
  rw [← hParts] at hWeights
  refine ⟨activeRowSet rowPart, activeColumnSet columnPart, ?_, ?_, ?_⟩
  · rw [hParts]
    exact supportCovered_add_activeParts rowPart columnPart
  · apply (Nat.le_div_iff_mul_le hPositiveB).mpr
    exact (activeRowSet_card_mul_distance_le CB distanceB hDistanceB rowPart hRow).trans
      hWeights.1
  · apply (Nat.le_div_iff_mul_le hPositiveA).mpr
    exact (activeColumnSet_card_mul_distance_le CA distanceA hDistanceA
      columnPart hColumn).trans hWeights.2
private theorem minimumDistance_positive
    {A : Type v} [Fintype A] (code : LinearCode (ZMod 2) A)
    {distance : Nat} (hDistance : MinimumDistance code distance) : 0 < distance := by
  obtain ⟨word, _, hNonzero, hWeight, _⟩ := hDistance
  rw [← hWeight]
  exact Nat.pos_of_ne_zero fun hZero =>
    hNonzero ((HammingWeight_eq_zero_iff word).mp hZero)
private theorem isRobust_of_supportCover_budget
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB p w : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB)
    (hCovers : ∀ x, x ∈ (dualTensorCode CA CB).carrier → HammingWeight x ≤ w →
      ∃ rows : Finset A, ∃ columns : Finset B,
        SupportCovered x rows columns ∧ rows.card ≤ p ∧ columns.card ≤ p) :
    IsRobust CA CB w := by
  intro dA dB hMinimumA hMinimumB x hx hWeight
  have hPositiveA := minimumDistance_positive CA hMinimumA
  have hPositiveB := minimumDistance_positive CB hMinimumB
  obtain ⟨wordA, hWordA, hNonzeroA, hWeightA, hMinA⟩ := hMinimumA
  obtain ⟨wordB, hWordB, hNonzeroB, hWeightB, hMinB⟩ := hMinimumB
  have hLowerA : distanceA ≤ dA := by
    rw [← hWeightA]
    exact hDistanceA wordA hWordA hNonzeroA
  have hLowerB : distanceB ≤ dB := by
    rw [← hWeightB]
    exact hDistanceB wordB hWordB hNonzeroB
  obtain ⟨rows, columns, hCovered, hRowCard, hColumnCard⟩ := hCovers x hx hWeight
  exact exists_distanceNormalized_supportCover CA CB dA dB hMinA hMinB
    hPositiveA hPositiveB x hx rows columns (by omega) (by omega) hCovered
private theorem not_isRobust_imp_noSmallCover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB p w : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB)
    (hNotRobust : ¬ IsRobust CA CB w) :
    ∃ x : Word (ZMod 2) (A × B),
      x ∈ (dualTensorCode CA CB).carrier ∧ HammingWeight x ≤ w ∧
        ∀ rows : Finset A, ∀ columns : Finset B,
          rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns := by
  by_contra hNoWitness
  apply hNotRobust
  apply isRobust_of_supportCover_budget CA CB distanceA distanceB p w
    hDistanceA hDistanceB hRows hColumns
  intro x hx hWeight
  by_contra hNoCover
  apply hNoWitness
  refine ⟨x, hx, hWeight, ?_⟩
  intro rows columns hRowCard hColumnCard hCovered
  exact hNoCover ⟨rows, columns, hCovered, hRowCard, hColumnCard⟩
private theorem hammingSupport_puncture_image
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    (hammingSupport (punctureMap removed x)).image Subtype.val =
      hammingSupport x \ removed := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, j.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro hi
    rcases Finset.mem_sdiff.mp hi with ⟨hSupport, hKept⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨i, hKept⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hSupport).2⟩
private theorem hammingWeight_eq_puncture_add_deleted
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight x = HammingWeight (punctureMap removed x) +
      (hammingSupport x ∩ removed).card := by
  classical
  have hCard := congrArg Finset.card (hammingSupport_puncture_image removed x)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hCard
  exact (Finset.card_sdiff_add_card_inter (hammingSupport x) removed).symm.trans
    (congrArg (fun n => n + (hammingSupport x ∩ removed).card) hCard.symm)
private theorem hammingWeight_puncture_loss_le
    {ι : Type v} [Fintype ι] (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight x ≤ HammingWeight (punctureMap removed x) + removed.card := by
  classical
  rw [hammingWeight_eq_puncture_add_deleted removed x]
  exact Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
private theorem hasMinimumDistanceAtLeast_puncturedCode
    {ι : Type v} [Fintype ι] (code : LinearCode (ZMod 2) ι)
    (distance : Nat) (removed : Finset ι)
    (hDistance : HasMinimumDistanceAtLeast code distance) :
    HasMinimumDistanceAtLeast (puncturedCode code removed) (distance - removed.card) := by
  intro x hx hNonzero
  rcases (mem_puncturedCode code removed x).mp hx with ⟨y, hy, rfl⟩
  have hY : y ≠ 0 := by
    intro hZero
    apply hNonzero
    simp [hZero]
  have hLower := hDistance y hy hY
  have hLoss := hammingWeight_puncture_loss_le removed y
  omega
private theorem hasMinimumDistanceAtLeast_puncturedCode_of_card_le
    {ι : Type v} [Fintype ι] (code : LinearCode (ZMod 2) ι)
    (distance budget : Nat) (removed : Finset ι)
    (hDistance : HasMinimumDistanceAtLeast code distance)
    (hCard : removed.card ≤ budget) :
    HasMinimumDistanceAtLeast (puncturedCode code removed) (distance - budget) := by
  intro x hx hNonzero
  have h := hasMinimumDistanceAtLeast_puncturedCode code distance removed
    hDistance x hx hNonzero
  omega
private theorem retained_syndrome_row_mem_puncturedCode
    {A B R : Type v} [Fintype A] [Fintype B] [Fintype R]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (check : Matrix R A (ZMod 2))
    (hCheck : CA.carrier ≤ LinearMap.ker (Matrix.toLin' check))
    (removed : Finset B)
    (retained : Word (ZMod 2) (A × KeptCoordinate removed))
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (hRetained : (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1)) = retained)
    (r : R) :
    (fun b => Matrix.mulVec check (columnRestriction b retained) r) ∈
      (puncturedCode CB removed).carrier := by
  apply (mem_puncturedCode CB removed _).mpr
  refine ⟨(fun b => Matrix.mulVec check (columnRestriction b x) r),
    syndrome_row_mem_of_mem_dualTensorCode CA CB check hCheck x hx r, ?_⟩
  funext b
  change Matrix.mulVec check (fun a => x (a, b.1)) r =
    Matrix.mulVec check (columnRestriction b retained) r
  have hColumn : (fun a => x (a, b.1)) = columnRestriction b retained := by
    funext a
    exact congrFun hRetained (a, b)
  rw [hColumn]
private theorem card_puncturedCheckRowsEvent_mul_pow_le
    {R B T : Type v} [Fintype B] [Fintype T]
    (removed : Finset B) (rows : R → Word (ZMod 2) (KeptCoordinate removed)) :
    Nat.card {matrix : Matrix T B (ZMod 2) // ∀ r, rows r ∈
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} *
      2 ^ (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range rows)) *
        (Fintype.card T - removed.card)) ≤ Nat.card (Matrix T B (ZMod 2)) := by
  rw [Nat.card_congr (puncturedCheckRowsEventEquiv removed rows)]
  exact card_puncturedCheckMatrixEvent_mul_pow_le removed
    (Submodule.span (ZMod 2) (Set.range rows))
private theorem card_puncturedCheckRowsEvent_mul_pow_le_of_rank_le
    {R B T : Type v} [Fintype B] [Fintype T]
    (removed : Finset B) (rows : R → Word (ZMod 2) (KeptCoordinate removed))
    (rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range rows))) :
    Nat.card {matrix : Matrix T B (ZMod 2) // ∀ r, rows r ∈
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} *
      2 ^ (rank * (Fintype.card T - removed.card)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_puncturedCheckRowsEvent_mul_pow_le removed rows)
  apply Nat.mul_le_mul_left
  exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
    (Nat.mul_le_mul_right _ hRank)
private theorem nat_card_event_le_of_imp
    {α : Type*} [Finite α] (P Q : α → Prop) (h : ∀ a, P a → Q a) :
    Nat.card {a : α // P a} ≤ Nat.card {a : α // Q a} := by
  apply Nat.card_le_card_of_injective (fun a => ⟨a.1, h a.1 a.2⟩)
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun c : {a : α // Q a} => c.1) hab
private theorem card_dualTensorRetainedEvent_mul_pow_le
    {A B R T : Type v} [Fintype A] [Fintype B] [Fintype R] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (check : Matrix R A (ZMod 2))
    (hCheck : CA.carrier ≤ LinearMap.ker (Matrix.toLin' check))
    (removed : Finset B) (retained : Word (ZMod 2) (A × KeptCoordinate removed))
    (rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun r : R =>
        (fun b => Matrix.mulVec check (columnRestriction b retained) r)))) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × B),
        x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
        (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - removed.card)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_puncturedCheckRowsEvent_mul_pow_le_of_rank_le
    removed (fun r b => Matrix.mulVec check (columnRestriction b retained) r) rank hRank)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hEvent
  obtain ⟨x, hx, hRetained⟩ := hEvent
  intro r
  exact retained_syndrome_row_mem_puncturedCode CA
    (parityCheckKernelCode (Matrix.toLin' matrix)) check hCheck
    removed retained x hx hRetained r
private theorem card_dualTensorLightRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (retained : Word (ZMod 2) (A × KeptCoordinate removed))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate removed => columnRestriction b retained) :
          Set (Word (ZMod 2) A))))
    (hLight : ∀ b : KeptCoordinate removed,
      HammingWeight (columnRestriction b retained) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × B),
        x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
        (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - removed.card)) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  obtain ⟨check, hKernel⟩ := exists_squareParityCheckMatrix_ker_eq CA.carrier
  exact card_dualTensorRetainedEvent_mul_pow_le CA check hKernel.symm.le removed retained rank
    (check_lightColumns_rowSpan_rank_le CA check hKernel retained cutoff distance rank hRank hLight hBudget hDistance)
private theorem card_combinedPuncture
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) :
    (combinedPuncture removed more).card = removed.card + more.card := by
  classical
  have hDisjoint : Disjoint removed (more.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro b hb hImage
    rcases Finset.mem_image.mp hImage with ⟨c, hc, rfl⟩
    exact c.2 hb
  rw [combinedPuncture, Finset.card_union_of_disjoint hDisjoint,
    Finset.card_image_of_injective _ Subtype.val_injective]
private theorem exists_dualTensor_lift_punctured_right
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removed : Finset B) (x : Word (ZMod 2) (A × KeptCoordinate removed))
    (hx : x ∈ (dualTensorCode CA (puncturedCode CB removed)).carrier) :
    ∃ y : Word (ZMod 2) (A × B), y ∈ (dualTensorCode CA CB).carrier ∧
      (fun ab : A × KeptCoordinate removed => y (ab.1, ab.2.1)) = x := by
  classical
  obtain ⟨columnPart, hColumn, rowPart, hRow, hParts⟩ := Submodule.mem_sup.mp hx
  have hPreimage : ∀ a : A, ∃ word : Word (ZMod 2) B,
      word ∈ CB.carrier ∧ punctureMap removed word = rowRestriction a rowPart := by
    intro a
    exact (mem_puncturedCode CB removed _).mp (hRow a)
  choose rowWord hRowWord hRowPuncture using hPreimage
  let liftedColumn : Word (ZMod 2) (A × B) := fun ab =>
    if hb : ab.2 ∈ removed then 0 else columnPart (ab.1, ⟨ab.2, hb⟩)
  let liftedRow : Word (ZMod 2) (A × B) := fun ab => rowWord ab.1 ab.2
  have hColumnLift : liftedColumn ∈ (columnCode (B := B) CA).carrier := by
    intro b
    by_cases hb : b ∈ removed
    · have hZero : columnRestriction b liftedColumn = 0 := by
        ext a
        simp [columnRestriction, liftedColumn, hb]
      rw [hZero]
      exact CA.carrier.zero_mem
    · have hKept : columnRestriction b liftedColumn =
        columnRestriction ⟨b, hb⟩ columnPart := by
        ext a
        simp [columnRestriction, liftedColumn, hb]
      rw [hKept]
      exact hColumn ⟨b, hb⟩
  have hRowLift : liftedRow ∈ (rowCode (A := A) CB).carrier := by
    intro a
    exact hRowWord a
  refine ⟨liftedColumn + liftedRow, ?_, ?_⟩
  · exact (dualTensorCode CA CB).carrier.add_mem
      (Submodule.mem_sup_left hColumnLift) (Submodule.mem_sup_right hRowLift)
  · funext ab
    have hRowValue := congrFun (hRowPuncture ab.1) ab.2
    change rowWord ab.1 ab.2.1 = rowPart ab at hRowValue
    change liftedColumn (ab.1, ab.2.1) + rowWord ab.1 ab.2.1 = x ab
    simp only [liftedColumn, dif_neg ab.2.2, hRowValue]
    exact congrFun hParts ab
private theorem card_puncturedDualTensorLightRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate (combinedPuncture removed more)))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
          columnRestriction b retained) : Set (Word (ZMod 2) A))))
    (hLight : ∀ b : KeptCoordinate (combinedPuncture removed more),
      HammingWeight (columnRestriction b retained) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        (fun ab : A × KeptCoordinate (combinedPuncture removed more) =>
          x (ab.1, ((nestedKeptCoordinateEquiv removed more).symm ab.2).1)) = retained} *
      2 ^ (rank * (Fintype.card T - (removed.card + more.card))) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  rw [← card_combinedPuncture removed more]
  apply le_trans _ (card_dualTensorLightRetainedEvent_mul_pow_le
    CA (combinedPuncture removed more) retained cutoff distance rank
    hRank hLight hBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hEvent
  rcases hEvent with ⟨x, hx, hRetained⟩
  obtain ⟨y, hy, hLift⟩ := exists_dualTensor_lift_punctured_right
    CA (parityCheckKernelCode (Matrix.toLin' matrix)) removed x hx
  refine ⟨y, hy, ?_⟩
  funext ab
  have hLiftValue := congrFun hLift
    (ab.1, ((nestedKeptCoordinateEquiv removed more).symm ab.2).1)
  exact hLiftValue.trans (congrFun hRetained ab)
private theorem columnRestriction_canonicalNestedRetainedWord
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more))
    (b : KeptCoordinate (combinedPuncture removed more)) :
    columnRestriction b (canonicalNestedRetainedWord removed more retained) =
      columnRestriction ((nestedKeptCoordinateEquiv removed more).symm b) retained := by
  rfl
private theorem canonicalNestedRetainedWord_columnFamily_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) :
    (Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
      columnRestriction b (canonicalNestedRetainedWord removed more retained)) =
    (Finset.univ.image fun b : KeptCoordinate more => columnRestriction b retained) := by
  classical
  ext word
  constructor
  · intro hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    exact Finset.mem_image.mpr
      ⟨(nestedKeptCoordinateEquiv removed more).symm b, Finset.mem_univ _, rfl⟩
  · intro hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    refine Finset.mem_image.mpr
      ⟨nestedKeptCoordinateEquiv removed more b, Finset.mem_univ _, ?_⟩
    simp only [columnRestriction_canonicalNestedRetainedWord, Equiv.symm_apply_apply]
private theorem canonicalNestedRetainedWord_columnSpan_rank_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
        columnRestriction b (canonicalNestedRetainedWord removed more retained)) :
          Set (Word (ZMod 2) A))) =
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate more => columnRestriction b retained) :
        Set (Word (ZMod 2) A))) := by
  rw [canonicalNestedRetainedWord_columnFamily_eq]
private theorem canonicalNestedRetainedWord_light
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) (cutoff : Nat)
    (hLight : ∀ b, HammingWeight (columnRestriction b retained) ≤ cutoff) :
    ∀ b, HammingWeight
      (columnRestriction b (canonicalNestedRetainedWord removed more retained)) ≤ cutoff := by
  intro b
  rw [columnRestriction_canonicalNestedRetainedWord]
  exact hLight _
private theorem card_nestedPuncturedDualTensorLightRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more))
    (cutoff distance rank : Nat)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate more =>
          columnRestriction b retained) : Set (Word (ZMod 2) A))))
    (hLight : ∀ b : KeptCoordinate more,
      HammingWeight (columnRestriction b retained) ≤ cutoff)
    (hBudget : rank * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        (fun ab : A × KeptCoordinate more => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - (removed.card + more.card))) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  have hCanonicalRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate (combinedPuncture removed more) =>
          columnRestriction b (canonicalNestedRetainedWord removed more retained)) :
            Set (Word (ZMod 2) A))) := by
    rw [canonicalNestedRetainedWord_columnSpan_rank_eq]
    exact hRank
  apply le_trans _ (card_puncturedDualTensorLightRetainedEvent_mul_pow_le
    CA removed more (canonicalNestedRetainedWord removed more retained)
    cutoff distance rank hCanonicalRank
    (canonicalNestedRetainedWord_light removed more retained cutoff hLight) hBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hEvent
  obtain ⟨x, hx, hRetained⟩ := hEvent
  refine ⟨x, hx, ?_⟩
  funext ab
  exact congrFun hRetained
    (ab.1, (nestedKeptCoordinateEquiv removed more).symm ab.2)
private theorem retainedColumnFamily_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (removed : Finset B) :
    (Finset.univ.image fun b : KeptCoordinate removed =>
      columnRestriction b (fun ab : A × KeptCoordinate removed => x (ab.1, ab.2.1))) =
      (Finset.univ.filter fun b : B => b ∉ removed).image
        (fun b => columnRestriction b x) := by
  classical
  ext word
  constructor
  · intro hword
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hword
    exact Finset.mem_image.mpr
      ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, rfl⟩
  · intro hword
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
    exact Finset.mem_image.mpr
      ⟨⟨b, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, rfl⟩
private theorem retainedLightColumnFamily_eq
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) :
    (Finset.univ.image fun b : KeptCoordinate
        (Finset.univ.filter fun b : B => cutoff < HammingWeight (columnRestriction b x)) =>
      columnRestriction b (fun ab => x (ab.1, ab.2.1))) =
      (Finset.univ.filter fun b : B =>
        HammingWeight (columnRestriction b x) ≤ cutoff).image
          (fun b => columnRestriction b x) := by
  classical
  rw [retainedColumnFamily_eq]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
private theorem retainedLightColumnSpan_rank_le
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff w p : Nat)
    (hCutoff : 0 < cutoff) (hWeight : HammingWeight x ≤ w)
    (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hNoCover : ∀ rows : Finset A, ∀ columns : Finset B,
      rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns) :
    p / cutoff + 1 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun b : KeptCoordinate
          (Finset.univ.filter fun b : B =>
            cutoff < HammingWeight (columnRestriction b x)) =>
          columnRestriction b (fun ab => x (ab.1, ab.2.1))) :
            Set (Word (ZMod 2) A))) := by
  rw [retainedLightColumnFamily_eq]
  apply Nat.succ_le_iff.mpr
  apply (Nat.div_lt_iff_lt_mul hCutoff).mpr
  exact puncture_lightColumnSpan_rank_mul_gt_budget x cutoff w p
    hWeight hHeavyBudget hNoCover
private theorem card_mul_two_pow_le_of_puncture_le
    {eventCard rank checkRows removed budget sampleCard : Nat}
    (hRemoved : removed ≤ budget)
    (hCount : eventCard * 2 ^ (rank * (checkRows - removed)) ≤ sampleCard) :
    eventCard * 2 ^ (rank * (checkRows - budget)) ≤ sampleCard := by
  apply le_trans _ hCount
  apply Nat.mul_le_mul_left
  exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
    (Nat.mul_le_mul_left rank (Nat.sub_le_sub_left hRemoved checkRows))
private theorem nat_card_exists_le_sum
    {ι α : Type v} [Fintype ι] [Finite α] (event : ι → α → Prop) :
    Nat.card {a : α // ∃ i, event i a} ≤ ∑ i, Nat.card {a : α // event i a} := by
  classical
  let project : (Σ i, {a : α // event i a}) → {a : α // ∃ i, event i a} :=
    fun x => ⟨x.2.1, x.1, x.2.2⟩
  have hSurj : Function.Surjective project := by
    intro a
    obtain ⟨i, hi⟩ := a.2
    exact ⟨⟨i, a.1, hi⟩, Subtype.ext rfl⟩
  calc
    _ ≤ Nat.card (Σ i, {a : α // event i a}) :=
      Nat.card_le_card_of_surjective project hSurj
    _ = _ := Nat.card_sigma
private theorem nat_card_exists_mul_le
    {ι α : Type v} [Fintype ι] [Finite α] (event : ι → α → Prop)
    (factor bound : Nat) (hCount : ∀ i, Nat.card {a : α // event i a} * factor ≤ bound) :
    Nat.card {a : α // ∃ i, event i a} * factor ≤ Nat.card ι * bound := by
  classical
  calc
    _ ≤ (∑ i, Nat.card {a : α // event i a}) * factor :=
      Nat.mul_le_mul_right factor (nat_card_exists_le_sum event)
    _ = ∑ i, Nat.card {a : α // event i a} * factor := by rw [Finset.sum_mul]
    _ ≤ ∑ _i : ι, bound := Finset.sum_le_sum fun i _ => hCount i
    _ = Nat.card ι * bound := by simp [Nat.card_eq_fintype_card]
private theorem nat_card_exists_valid_mul_le
    {ι α : Type v} [Fintype ι] [Finite α] (valid : ι → Prop) (event : ι → α → Prop)
    (factor bound : Nat)
    (hCount : ∀ i, valid i → Nat.card {a : α // event i a} * factor ≤ bound) :
    Nat.card {a : α // ∃ i, valid i ∧ event i a} * factor ≤ Nat.card ι * bound := by
  classical
  apply nat_card_exists_mul_le (fun i a => valid i ∧ event i a)
  intro i
  by_cases hi : valid i
  · exact le_trans (Nat.mul_le_mul_right factor
      (nat_card_event_le_of_imp _ _ fun _ h => h.2)) (hCount i hi)
  · have hEmpty : IsEmpty {a : α // valid i ∧ event i a} :=
      ⟨fun a => hi a.2.1⟩
    have hZero : Nat.card {a : α // valid i ∧ event i a} = 0 :=
      Nat.card_eq_zero.mpr (Or.inl hEmpty)
    rw [hZero, Nat.zero_mul]
    exact Nat.zero_le _
private theorem card_allPuncturedLightMatrixFamily_le
    (A B : Type v) [Fintype A] [Fintype B] [DecidableEq A] (cutoff : Nat) :
    Nat.card (AllPuncturedLightMatrixFamily A B cutoff) ≤
      2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  let volume := ∑ weight ∈ Finset.range (cutoff + 1),
    Nat.choose (Fintype.card A) weight
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range (cutoff + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
    simpa [volume] using (Finset.single_le_sum
      (fun weight _ => Nat.zero_le (Nat.choose (Fintype.card A) weight)) hzero)
  calc
    _ = ∑ removed : Finset B,
        Nat.card {x : Word (ZMod 2) (A × KeptCoordinate removed) //
          ∀ b : KeptCoordinate removed, HammingWeight (columnRestriction b x) < cutoff + 1} :=
      Nat.card_sigma
    _ = ∑ removed : Finset B, volume ^ (Fintype.card B - removed.card) := by
      apply Finset.sum_congr rfl
      intro removed _
      have h := card_lowWeightColumnMatrices A (KeptCoordinate removed) (cutoff + 1)
      rw [card_keptCoordinate] at h
      rw [Fintype.card_eq_nat_card] at h
      exact h
    _ ≤ ∑ _removed : Finset B, volume ^ Fintype.card B :=
      Finset.sum_le_sum fun removed _ => pow_le_pow_right₀ hOne (Nat.sub_le _ _)
    _ = 2 ^ Fintype.card B * volume ^ Fintype.card B := by
      simp [Fintype.card_finset]
private theorem rawColumnSpanRank_eq_range
    {A C : Type v} [Fintype A] [Fintype C] (x : Word (ZMod 2) (A × C)) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        ((Finset.univ.image fun c : C => columnRestriction c x) : Set (Word (ZMod 2) A))) =
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun c : C => fun a : A => x (a, c))) := by
  have hFamily :
      ((Finset.univ.image fun c : C => columnRestriction c x) : Set (Word (ZMod 2) A)) =
        Set.range (fun c : C => fun a : A => x (a, c)) := by
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  exact congrArg (fun s : Set (Word (ZMod 2) A) =>
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) s)) hFamily
private theorem card_noSmallCoverCompletionEvent_mul_le
    {A C α : Type v} [Fintype A] [Fintype C] [Finite α]
    (membership : Word (ZMod 2) (A × C) → α → Prop)
    (cutoff w p factor : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hCount : ∀ more : Finset C,
      ∀ retained : Word (ZMod 2) (A × KeptCoordinate more),
      (∀ b : KeptCoordinate more, HammingWeight (columnRestriction b retained) < cutoff + 1) →
      more.card ≤ p →
      p / cutoff + 1 ≤ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (Set.range fun b : KeptCoordinate more => fun a : A => retained (a, b))) →
      Nat.card {a : α // ∃ x, membership x a ∧
        (fun ab : A × KeptCoordinate more => x (ab.1, ab.2.1)) = retained} * factor ≤
          Nat.card α) :
    Nat.card {a : α // ∃ x, membership x a ∧ HammingWeight x ≤ w ∧
      ∀ rows : Finset A, ∀ columns : Finset C,
        rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns} * factor ≤
      (2 ^ Fintype.card C * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card C) * Nat.card α := by
  classical
  let valid : AllPuncturedLightMatrixFamily A C cutoff → Prop := fun i =>
    i.1.card ≤ p ∧ p / cutoff + 1 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun b : KeptCoordinate i.1 => fun a : A => i.2.1 (a, b)))
  let completion : AllPuncturedLightMatrixFamily A C cutoff → α → Prop :=
    fun i a => ∃ x, membership x a ∧
      (fun ab : A × KeptCoordinate i.1 => x (ab.1, ab.2.1)) = i.2.1
  have hUnion : Nat.card {a : α // ∃ i : AllPuncturedLightMatrixFamily A C cutoff,
      valid i ∧ completion i a} * factor ≤
      (2 ^ Fintype.card C * (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card C) * Nat.card α := by
    apply le_trans _ (Nat.mul_le_mul_right _ (card_allPuncturedLightMatrixFamily_le A C cutoff))
    apply nat_card_exists_valid_mul_le
      valid completion
    intro i hi
    exact hCount i.1 i.2.1 i.2.2 hi.1 hi.2
  apply le_trans _ hUnion
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro a hBad
  obtain ⟨x, hx, hWeight, hNoCover⟩ := hBad
  let more := Finset.univ.filter fun b : C => cutoff < HammingWeight (columnRestriction b x)
  have hLight : ∀ b : KeptCoordinate more,
      HammingWeight (columnRestriction b (fun ab => x (ab.1, ab.2.1))) < cutoff + 1 := by
    intro b
    apply Nat.lt_succ_of_le
    apply Nat.le_of_not_gt
    intro hHeavy
    exact b.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHeavy⟩)
  let i : AllPuncturedLightMatrixFamily A C cutoff :=
    ⟨more, (fun ab => x (ab.1, ab.2.1)), hLight⟩
  refine ⟨i, ⟨?_, ?_⟩, x, hx, rfl⟩
  · exact heavyColumns_card_le_punctureBudget x cutoff w p hWeight hHeavyBudget
  · have hRank := retainedLightColumnSpan_rank_le x cutoff w p hCutoff hWeight hHeavyBudget hNoCover
    rw [rawColumnSpanRank_eq_range] at hRank
    exact hRank
private theorem card_budgetedNestedRetainedEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more))
    (cutoff p distance rank : Nat)
    (hLight : ∀ b : KeptCoordinate more, HammingWeight (columnRestriction b retained) < cutoff + 1)
    (hCard : more.card ≤ p)
    (hRank : rank ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (Set.range fun b : KeptCoordinate more => fun a : A => retained (a, b))))
    (hBudget : rank * cutoff < distance) (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        (fun ab : A × KeptCoordinate more => x (ab.1, ab.2.1)) = retained} *
      2 ^ (rank * (Fintype.card T - (removed.card + p))) ≤
      Nat.card (Matrix T B (ZMod 2)) := by
  apply card_mul_two_pow_le_of_puncture_le
    (removed := removed.card + more.card) (Nat.add_le_add_left hCard removed.card)
  exact card_nestedPuncturedDualTensorLightRetainedEvent_mul_pow_le
    CA removed more retained cutoff distance rank
    (by rw [rawColumnSpanRank_eq_range]; exact hRank)
    (fun b => Nat.le_of_lt_succ (hLight b)) hBudget hDistance
private theorem card_puncturedNoSmallCoverDualTensorEvent_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B) (cutoff w p distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance)
    (hDistance : HasMinimumDistanceAtLeast CA distance) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
        x ∈ (dualTensorCode CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
        HammingWeight x ≤ w ∧
        ∀ rows : Finset A, ∀ columns : Finset (KeptCoordinate removed),
          rows.card ≤ p → columns.card ≤ p → ¬ SupportCovered x rows columns} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (removed.card + p))) ≤
      (2 ^ Fintype.card (KeptCoordinate removed) *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card (KeptCoordinate removed)) *
          Nat.card (Matrix T B (ZMod 2)) := by
  apply card_noSmallCoverCompletionEvent_mul_le
    (fun x matrix => x ∈ (dualTensorCode CA
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier)
    cutoff w p _ hCutoff hHeavyBudget
  intro more retained hLight hCard hRank
  exact card_budgetedNestedRetainedEvent_mul_pow_le
    CA removed more retained cutoff p distance (p / cutoff + 1)
    hLight hCard hRank hSyndromeBudget hDistance
private theorem card_notRobust_distanceGoodPuncturedKernel_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B)
    (cutoff w p distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA) (hColumns : 2 * p ≤ distanceB - removed.card) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust CA
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed) w} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (removed.card + p))) ≤
      (2 ^ Fintype.card (KeptCoordinate removed) *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card (KeptCoordinate removed)) *
          Nat.card (Matrix T B (ZMod 2)) := by
  apply le_trans _ (card_puncturedNoSmallCoverDualTensorEvent_mul_pow_le
    CA removed cutoff w p distanceA hCutoff hHeavyBudget hSyndromeBudget hDistance)
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hBad
  exact not_isRobust_imp_noSmallCover CA
    (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)
    distanceA (distanceB - removed.card) p w hDistance
    (hasMinimumDistanceAtLeast_puncturedCode _ distanceB removed hBad.1)
    hRows hColumns hBad.2
private theorem puncturedLightIndexBound_le
    {A B : Type v} [Fintype A] [Fintype B]
    (removedA : Finset A) (removedB : Finset B) (cutoff : Nat) :
    (2 ^ Fintype.card (KeptCoordinate removedB) *
      (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card (KeptCoordinate removedA)) weight) ^
          Fintype.card (KeptCoordinate removedB)) ≤
      2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B := by
  classical
  let volume := ∑ weight ∈ Finset.range (cutoff + 1),
    Nat.choose (Fintype.card A) weight
  have hA : Fintype.card (KeptCoordinate removedA) ≤ Fintype.card A := by
    rw [card_keptCoordinate]
    exact Nat.sub_le _ _
  have hB : Fintype.card (KeptCoordinate removedB) ≤ Fintype.card B := by
    rw [card_keptCoordinate]
    exact Nat.sub_le _ _
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range (cutoff + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
    simpa [volume] using (Finset.single_le_sum
      (fun weight _ => Nat.zero_le (Nat.choose (Fintype.card A) weight)) hzero)
  apply Nat.mul_le_mul
  · exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat)) hB
  · apply le_trans (Nat.pow_le_pow_left
      (Finset.sum_le_sum fun weight _ => Nat.choose_le_choose weight hA) _)
    exact pow_le_pow_right₀ hOne hB
private theorem card_matchingPuncturedRobustFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removedA : Finset A) (removedB : Finset B)
    (cutoff w p q distanceA distanceB : Nat)
    (hMatching : removedA.card = removedB.card) (hCard : removedA.card ≤ q)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA - q)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA - q) (hColumns : 2 * p ≤ distanceB - q) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust (puncturedCode CA removedA)
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removedB) w} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      (2 ^ Fintype.card B *
        (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
            Nat.card (Matrix T B (ZMod 2)) := by
  have hBCard : removedB.card ≤ q := by omega
  have hCount := card_notRobust_distanceGoodPuncturedKernel_mul_pow_le (T := T)
    (puncturedCode CA removedA) removedB cutoff w p (distanceA - q) distanceB
    hCutoff hHeavyBudget hSyndromeBudget
    (hasMinimumDistanceAtLeast_puncturedCode_of_card_le CA distanceA q removedA hDistance hCard)
    hRows (by omega)
  have hBudgeted := card_mul_two_pow_le_of_puncture_le
    (removed := removedB.card + p) (budget := q + p)
    (Nat.add_le_add_right hBCard p) hCount
  exact le_trans hBudgeted (Nat.mul_le_mul_right _
    (puncturedLightIndexBound_le removedA removedB cutoff))
private theorem card_matchingPunctureIndex
    (A B : Type v) [Fintype A] [Fintype B] (q : Nat) :
    Nat.card (MatchingPunctureIndex A B q) =
      ∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size := by
  classical
  simp [MatchingPunctureIndex, Nat.card_eq_fintype_card,
    Fintype.card_sigma, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro size hSize
  simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hSize)]
private theorem card_notPunctureResistant_distanceGoodKernel_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA - q)
    (hDistance : HasMinimumDistanceAtLeast CA distanceA)
    (hRows : 2 * p ≤ distanceA - q) (hColumns : 2 * p ≤ distanceB - q) :
    Nat.card {matrix : Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobustWithPunctureResistance CA
          (parityCheckKernelCode (Matrix.toLin' matrix)) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      (∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        ((2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
              Nat.card (Matrix T B (ZMod 2))) := by
  classical
  let event : MatchingPunctureIndex A B q → Matrix T B (ZMod 2) → Prop :=
    fun i matrix =>
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' matrix)) distanceB ∧
        ¬ IsRobust (puncturedCode CA i.2.1.1)
          (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) i.2.2.1) w
  have hUnion := nat_card_exists_mul_le event
    (2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))))
    ((2 ^ Fintype.card B *
      (∑ weight ∈ Finset.range (cutoff + 1),
        Nat.choose (Fintype.card A) weight) ^ Fintype.card B) *
          Nat.card (Matrix T B (ZMod 2)))
    (fun i => card_matchingPuncturedRobustFailure_mul_pow_le
      CA i.2.1.1 i.2.2.1 cutoff w p q distanceA distanceB
      (i.2.1.2.trans i.2.2.2.symm) (by have h := i.1.2; have hA := i.2.1.2; omega)
      hCutoff hHeavyBudget hSyndromeBudget hDistance hRows hColumns)
  rw [card_matchingPunctureIndex] at hUnion
  apply le_trans _ hUnion
  apply Nat.mul_le_mul_right
  apply nat_card_event_le_of_imp
  intro matrix hBad
  have hNot := hBad.2
  simp only [IsRobustWithPunctureResistance] at hNot
  push Not at hNot
  obtain ⟨removedA, removedB, hMatching, hCard, hFail⟩ := hNot
  let i : MatchingPunctureIndex A B q :=
    ⟨⟨removedA.card, Nat.lt_succ_of_le hCard⟩,
      ⟨removedA, rfl⟩, ⟨removedB, hMatching.symm⟩⟩
  exact ⟨i, hBad.1, hFail⟩
private theorem nat_card_product_event_mul_le
    {α β : Type v} [Fintype α] [Finite β]
    (event : α × β → Prop) (factor bound : Nat)
    (hCount : ∀ first, Nat.card {second : β // event (first, second)} *
      factor ≤ bound) :
    Nat.card {sample : α × β // event sample} * factor ≤
      Nat.card α * bound := by
  classical
  rw [Nat.card_congr (productEventFiberEquiv event),
    Nat.card_sigma, Finset.sum_mul]
  calc
    _ ≤ ∑ _first : α, bound := Finset.sum_le_sum fun first _ => hCount first
    _ = Nat.card α * bound := by simp [Nat.card_eq_fintype_card]
private theorem card_jointPrimalPunctureFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceA - q)
    (hRows : 2 * p ≤ distanceA - q) (hColumns : 2 * p ≤ distanceB - q) :
    Nat.card {sample : Matrix T A (ZMod 2) × Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' sample.1)) distanceA ∧
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' sample.2)) distanceB ∧
      ¬ IsRobustWithPunctureResistance
        (parityCheckRowCode (Matrix.toLin' sample.1))
        (parityCheckKernelCode (Matrix.toLin' sample.2)) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        (2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B)) *
              Nat.card (Matrix T A (ZMod 2) × Matrix T B (ZMod 2)) := by
  classical
  let numerator :=
    (∑ size ∈ Finset.range (q + 1),
      Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        (2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B)
  apply le_trans (nat_card_product_event_mul_le _
    (2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))))
    (numerator * Nat.card (Matrix T B (ZMod 2))) ?_)
  · rw [Nat.card_prod]
    change Nat.card (Matrix T A (ZMod 2)) *
      (numerator * Nat.card (Matrix T B (ZMod 2))) ≤
        numerator * (Nat.card (Matrix T A (ZMod 2)) * Nat.card (Matrix T B (ZMod 2)))
    exact le_of_eq (by ring)
  · intro first
    by_cases hFirst :
        HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' first)) distanceA
    · have hCount := card_notPunctureResistant_distanceGoodKernel_mul_pow_le (B := B) (T := T)
        (parityCheckRowCode (Matrix.toLin' first)) cutoff w p q distanceA distanceB
        hCutoff hHeavyBudget hSyndromeBudget hFirst hRows hColumns
      apply le_trans (Nat.mul_le_mul_right _
        (nat_card_event_le_of_imp _ _ fun _ h => h.2))
      simpa [numerator, Nat.mul_assoc] using hCount
    · have hEmpty : IsEmpty {second : Matrix T B (ZMod 2) //
          HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' first)) distanceA ∧
          HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' second)) distanceB ∧
          ¬ IsRobustWithPunctureResistance
            (parityCheckRowCode (Matrix.toLin' first))
            (parityCheckKernelCode (Matrix.toLin' second)) w q} :=
        ⟨fun second => hFirst second.2.1⟩
      rw [Nat.card_eq_zero.mpr (Or.inl hEmpty), Nat.zero_mul]
      exact Nat.zero_le _
private theorem card_jointSwappedPunctureFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceB - q)
    (hRows : 2 * p ≤ distanceB - q) (hColumns : 2 * p ≤ distanceA - q) :
    Nat.card {sample : Matrix T A (ZMod 2) × Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' sample.1)) distanceA ∧
      HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' sample.2)) distanceB ∧
      ¬ IsRobustWithPunctureResistance
        (parityCheckKernelCode (Matrix.toLin' sample.1))
        (parityCheckRowCode (Matrix.toLin' sample.2)) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card B) size * Nat.choose (Fintype.card A) size) *
        (2 ^ Fintype.card A *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card B) weight) ^ Fintype.card A)) *
              Nat.card (Matrix T A (ZMod 2) × Matrix T B (ZMod 2)) := by
  classical
  have hCount := card_jointPrimalPunctureFailure_mul_pow_le (A := B) (B := A) (T := T)
    cutoff w p q distanceB distanceA hCutoff hHeavyBudget hSyndromeBudget hRows hColumns
  rw [Nat.card_congr (robustFailureSwapEquiv
    (fun first : Matrix T A (ZMod 2) => parityCheckKernelCode (Matrix.toLin' first))
    (fun second : Matrix T B (ZMod 2) => parityCheckRowCode (Matrix.toLin' second))
    distanceA distanceB w q)]
  simpa only [Nat.card_prod, Nat.mul_comm] using hCount
private theorem linearCode_eq_of_carrier_eq
    {F : Type u} {I : Type v} [Field F] [Fintype F] [Fintype I]
    {first second : LinearCode F I} (hCarrier : first.carrier = second.carrier) :
    first = second := by
  cases first
  cases second
  cases hCarrier
  rfl
private theorem parityCheckKernelCode_dual_eq_rowCode
    {I K : Type v} [Fintype I] [Fintype K]
    (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) :
    (parityCheckKernelCode P).dual = parityCheckRowCode P := by
  apply linearCode_eq_of_carrier_eq
  rw [← parityCheckRowCode_dual_eq_kernelCode P]
  exact dual_dual_carrier_eq _
private theorem card_jointDualPunctureFailure_mul_pow_le
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (cutoff w p q distanceA distanceB : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distanceB - q)
    (hRows : 2 * p ≤ distanceB - q) (hColumns : 2 * p ≤ distanceA - q) :
    Nat.card {sample : Matrix T A (ZMod 2) × Matrix T B (ZMod 2) //
      HasMinimumDistanceAtLeast (parityCheckRowCode (Matrix.toLin' sample.1)).dual distanceA ∧
      HasMinimumDistanceAtLeast (parityCheckKernelCode (Matrix.toLin' sample.2)).dual distanceB ∧
      ¬ IsRobustWithPunctureResistance
        ((parityCheckRowCode (Matrix.toLin' sample.1)).dual)
        ((parityCheckKernelCode (Matrix.toLin' sample.2)).dual) w q} *
      2 ^ ((p / cutoff + 1) * (Fintype.card T - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card B) size * Nat.choose (Fintype.card A) size) *
        (2 ^ Fintype.card A *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card B) weight) ^ Fintype.card A)) *
              Nat.card (Matrix T A (ZMod 2) × Matrix T B (ZMod 2)) := by
  have hCount := card_jointSwappedPunctureFailure_mul_pow_le (A := A) (B := B) (T := T)
    cutoff w p q distanceA distanceB hCutoff hHeavyBudget hSyndromeBudget hRows hColumns
  simpa only [parityCheckRowCode_dual_eq_kernelCode, parityCheckKernelCode_dual_eq_rowCode] using hCount
private theorem card_distanceGoodPunctureFailure_primal_mul_pow_le
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q false sample} *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card A) size * Nat.choose (Fintype.card B) size) *
        (2 ^ Fintype.card B *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card A) weight) ^ Fintype.card B)) *
              Nat.card (RandomLocalCodeSample r A B) := by
  have hSubset : Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q false sample} ≤
      Nat.card {sample : RandomLocalCodeSample r A B //
        HasMinimumDistanceAtLeast sample.codeA distance ∧
        HasMinimumDistanceAtLeast sample.codeB distance ∧
        ¬ IsRobustWithPunctureResistance sample.codeA sample.codeB w q} := by
    apply nat_card_event_le_of_imp
    intro sample h
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩
  apply le_trans (Nat.mul_le_mul_right _ hSubset)
  have hCount := card_jointPrimalPunctureFailure_mul_pow_le (A := A) (B := B) (T := ULift.{v} (Fin r))
    cutoff w p q distance distance hCutoff hHeavyBudget
    hSyndromeBudget hDistanceBudget hDistanceBudget
  simpa only [RandomLocalCodeSample.codeA, RandomLocalCodeSample.codeB,
    RandomLocalCodeSample, Fintype.card_ulift, Fintype.card_fin] using hCount
private theorem card_distanceGoodPunctureFailure_dual_mul_pow_le
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q true sample} *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      ((∑ size ∈ Finset.range (q + 1),
        Nat.choose (Fintype.card B) size * Nat.choose (Fintype.card A) size) *
        (2 ^ Fintype.card A *
          (∑ weight ∈ Finset.range (cutoff + 1),
            Nat.choose (Fintype.card B) weight) ^ Fintype.card A)) *
              Nat.card (RandomLocalCodeSample r A B) := by
  have hSubset : Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q true sample} ≤
      Nat.card {sample : RandomLocalCodeSample r A B //
        HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
        HasMinimumDistanceAtLeast sample.codeB.dual distance ∧
        ¬ IsRobustWithPunctureResistance sample.codeA.dual sample.codeB.dual w q} := by
    apply nat_card_event_le_of_imp
    intro sample h
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  apply le_trans (Nat.mul_le_mul_right _ hSubset)
  have hCount := card_jointDualPunctureFailure_mul_pow_le (A := A) (B := B) (T := ULift.{v} (Fin r))
    cutoff w p q distance distance hCutoff hHeavyBudget
    hSyndromeBudget hDistanceBudget hDistanceBudget
  simpa only [RandomLocalCodeSample.codeA, RandomLocalCodeSample.codeB,
    RandomLocalCodeSample, Fintype.card_ulift, Fintype.card_fin] using hCount
private theorem card_distanceGoodPunctureFailures_mul_pow_le
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    (∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample}) *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      2 * ((∑ size ∈ Finset.range (q + 1),
        Nat.choose Delta size * Nat.choose Delta size) *
        (2 ^ Delta * (∑ weight ∈ Finset.range (cutoff + 1),
          Nat.choose Delta weight) ^ Delta)) *
              Nat.card (RandomLocalCodeSample r A B) := by
  have hP := card_distanceGoodPunctureFailure_primal_mul_pow_le
    (r := r) (A := A) (B := B) cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  have hD := card_distanceGoodPunctureFailure_dual_mul_pow_le
    (r := r) (A := A) (B := B) cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  rw [hA, hB] at hP hD
  rw [Fintype.sum_bool, Nat.add_mul]
  exact (Nat.add_le_add hD hP).trans_eq (by ring)
private theorem card_distanceGoodPunctureFailures_mul_pow_le_pow_clog
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat) (hq : q ≤ Delta) (hc : cutoff ≤ Delta)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q) :
    (∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample}) *
      2 ^ ((p / cutoff + 1) * (r - (q + p))) ≤
      2 ^ (Delta + 1 + Nat.clog 2 (Delta + 1) *
        (2 * q + 1 + (cutoff + 1) * Delta)) *
          Nat.card (RandomLocalCodeSample r A B) := by
  have hCount := card_distanceGoodPunctureFailures_mul_pow_le
    (r := r) hA hB cutoff w p q distance
    hCutoff hHeavyBudget hSyndromeBudget hDistanceBudget
  exact hCount.trans (Nat.mul_le_mul_right _
    (robustIndexNumerator_le_pow_clog Delta q cutoff hq hc))
private theorem four_mul_card_distanceGoodPunctureFailures_le
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (cutoff w p q distance : Nat) (hq : q ≤ Delta) (hc : cutoff ≤ Delta)
    (hCutoff : 0 < cutoff) (hHeavyBudget : w < (p + 1) * (cutoff + 1))
    (hSyndromeBudget : (p / cutoff + 1) * cutoff < distance - q)
    (hDistanceBudget : 2 * p ≤ distance - q)
    (hGap : Delta + 1 + Nat.clog 2 (Delta + 1) *
      (2 * q + 1 + (cutoff + 1) * Delta) + 2 ≤
        (p / cutoff + 1) * (r - (q + p))) :
    4 * (∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample}) ≤
        Nat.card (RandomLocalCodeSample r A B) := by
  let E := Delta + 1 + Nat.clog 2 (Delta + 1) *
    (2 * q + 1 + (cutoff + 1) * Delta)
  let D := (p / cutoff + 1) * (r - (q + p))
  let C := ∑ dualSide : Bool, Nat.card {sample : RandomLocalCodeSample r A B //
    distanceGoodPunctureFailure distance w q dualSide sample}
  let S := Nat.card (RandomLocalCodeSample r A B)
  have hCount : C * 2 ^ D ≤ 2 ^ E * S :=
    card_distanceGoodPunctureFailures_mul_pow_le_pow_clog
      hA hB cutoff w p q distance hq hc hCutoff hHeavyBudget
      hSyndromeBudget hDistanceBudget
  have hPow : 4 * 2 ^ E ≤ 2 ^ D := by
    have h := pow_le_pow_right' (by decide : 1 ≤ (2 : Nat)) hGap
    simpa only [E, D, pow_add, show (2 : Nat) ^ 2 = 4 by norm_num,
      Nat.mul_comm] using h
  have hScaled : (4 * C) * 2 ^ D ≤ S * 2 ^ D := by
    calc
      (4 * C) * 2 ^ D = 4 * (C * 2 ^ D) := by ring
      _ ≤ 4 * (2 ^ E * S) := Nat.mul_le_mul_left 4 hCount
      _ = (4 * 2 ^ E) * S := by ring
      _ ≤ 2 ^ D * S := Nat.mul_le_mul_right S hPow
      _ = S * 2 ^ D := by ring
  exact Nat.le_of_mul_le_mul_right hScaled (by positivity : 0 < 2 ^ D)
private theorem exists_eventual_source_conditionedRobustness_quarter
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hRho : 0 < rho) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          4 * (∑ dualSide : Bool,
            Nat.card {sample : RandomLocalCodeSample (randomRowCount rho n) A B //
              distanceGoodPunctureFailure (Nat.floor (delta * n))
                (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)))
                (Nat.floor ((n : ℝ) ^ gamma)) dualSide sample}) ≤
            Nat.card (RandomLocalCodeSample (randomRowCount rho n) A B) := by
  have hBeta : 0 < min delta rho / 8 :=
    div_pos (lt_min hDelta hRho) (by norm_num)
  have hBetaRho : min delta rho / 8 ≤ rho / 4 := by
    have h := min_le_right delta rho
    linarith
  obtain ⟨tB, htB⟩ := exists_eventual_source_robustness_floor_budgets
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGamma hDelta hRho
  obtain ⟨tG, htG⟩ := exists_eventual_robustIndexExponent_add_two_le_syndrome
    ((1 : ℝ) / 2 - epsilon / 2) gamma (min delta rho / 8) rho
    (by linarith) (by linarith) hGamma hBeta hRho hBetaRho
  refine ⟨max tB tG, ?_⟩
  intro n hn A B _ _ hA hB
  obtain ⟨hK, hQ, hKN, hW, hRank, hCover⟩ :=
    htB n ((Nat.le_max_left _ _).trans hn)
  exact four_mul_card_distanceGoodPunctureFailures_le
    (r := randomRowCount rho n) hA hB
    (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 2 - epsilon / 2)))
    (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)))
    (Nat.floor ((min delta rho / 8) * n))
    (Nat.floor ((n : ℝ) ^ gamma)) (Nat.floor (delta * n))
    hQ hKN hK hW hRank hCover
    (htG n ((Nat.le_max_right _ _).trans hn))
private theorem hasPositiveUniformProbability_goodLocalCodeEvent_of_count_bound
    {r Delta distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      (∑ index : Sum
          (SimultaneousDistanceBadIndex r distanceThreshold A B) Bool,
        (eventFinset (goodLocalCodeBad
          distanceThreshold robustness punctures index)).card) <
      Fintype.card (RandomLocalCodeSample r A B)) :
    HasPositiveUniformProbability (Ω := RandomLocalCodeSample r A B)
      (GoodLocalCodeEvent (r := r) (A := A) (B := B)
        r (Delta - r) distanceThreshold robustness punctures) := by
  apply hasPositiveUniformProbability_of_union_bound
    (good := GoodLocalCodeEvent (r := r) (A := A) (B := B)
      r (Delta - r) distanceThreshold robustness punctures)
    (bad := goodLocalCodeBad distanceThreshold robustness punctures)
  · intro sample hnot
    by_cases hbase : sample.HasFullRowRank ∧
        HasMinimumDistanceAtLeast sample.codeA distanceThreshold ∧
        HasMinimumDistanceAtLeast sample.codeB distanceThreshold ∧
        HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold ∧
        HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold
    · obtain ⟨hFull, hDistanceA, hDistanceB, hDistanceADual,
        hDistanceBDual⟩ := hbase
      by_cases hRobust : IsRobustWithPunctureResistance
          sample.codeA sample.codeB robustness punctures
      · have hRobustDual : ¬ IsRobustWithPunctureResistance
            sample.codeA.dual sample.codeB.dual robustness punctures := by
          intro hDual
          exact hnot (goodLocalCodeEvent_of_fullRowRank hA hB hFull
            hDistanceA hDistanceB hDistanceADual hDistanceBDual hRobust hDual)
        exact ⟨.inr true, hDistanceA, hDistanceB, hDistanceADual,
          hDistanceBDual, hRobustDual⟩
      · exact ⟨.inr false, hDistanceA, hDistanceB, hDistanceADual,
          hDistanceBDual, hRobust⟩
    · obtain ⟨index, hindex⟩ :=
        simultaneousDistanceBad_covers sample hbase
      exact ⟨.inl index, hindex⟩
  · exact hcount
private theorem simultaneousDistance_twelvefold_bounds_of_real_margins
    (Delta r distance : Nat) (delta : ℝ)
    (hDelta : 0 < Delta) (hrDelta : r ≤ Delta) (hDistance : 0 < distance)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hDistanceCeil : distance = Nat.ceil (delta * Delta))
    (hceil : 2 ≤ distance)
    (hGeneratorMargin :
      12 * (((2 ^ r : Nat) : ℝ) *
        Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
        ((2 ^ Delta : Nat) : ℝ))
    (hKernelMargin :
      12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        ((2 ^ r : Nat) : ℝ)) :
    12 * (2 ^ r - 1) < 2 ^ Delta ∧
      12 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) <
        2 ^ Delta ∧
      12 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta := by
  let volume := ∑ weight ∈ Finset.range distance, Nat.choose Delta weight
  have hVolume : (volume : ℝ) ≤
      Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
    subst distance
    exact binaryHammingBall_le_exp_binEntropy_ceilRadius
      Delta delta hDelta hdeltaPositive hdeltaHalf hceil
  have hOne : 1 ≤ volume := by
    have hzero : 0 ∈ Finset.range distance := Finset.mem_range.mpr hDistance
    simpa [volume] using
      (Finset.single_le_sum
        (fun weight _ => Nat.zero_le (Nat.choose Delta weight)) hzero)
  have hGenerator : 12 * ((2 ^ r - 1) * volume) < 2 ^ Delta := by
    have hSub : (((2 ^ r - 1 : Nat) : ℝ)) ≤ ((2 ^ r : Nat) : ℝ) := by
      exact_mod_cast Nat.sub_le (2 ^ r) 1
    have hReal : (((12 * ((2 ^ r - 1) * volume) : Nat) : ℝ)) <
        ((2 ^ Delta : Nat) : ℝ) := by
      calc
        (((12 * ((2 ^ r - 1) * volume) : Nat) : ℝ)) =
            12 * ((2 ^ r - 1 : Nat) : ℝ) * (volume : ℝ) := by
              norm_cast
              ring
        _ ≤ 12 * ((2 ^ r : Nat) : ℝ) * (volume : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSub (by norm_num))
            (Nat.cast_nonneg _)
        _ ≤ 12 * ((2 ^ r : Nat) : ℝ) *
            Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          exact mul_le_mul_of_nonneg_left hVolume (by positivity)
        _ < ((2 ^ Delta : Nat) : ℝ) := by
          simpa only [mul_assoc] using hGeneratorMargin
    exact_mod_cast hReal
  have hRank : 12 * (2 ^ r - 1) < 2 ^ Delta := by
    have hLe : (2 ^ r - 1) ≤ (2 ^ r - 1) * volume := by
      calc
        2 ^ r - 1 = (2 ^ r - 1) * 1 := by omega
        _ ≤ (2 ^ r - 1) * volume :=
          Nat.mul_le_mul_left _ hOne
    exact (Nat.mul_le_mul_left 12 hLe).trans_lt hGenerator
  have hKernelSmall : 12 * volume < 2 ^ r := by
    have hReal : (((12 * volume : Nat) : ℝ)) < ((2 ^ r : Nat) : ℝ) := by
      calc
        (((12 * volume : Nat) : ℝ)) = 12 * (volume : ℝ) := by norm_cast
        _ ≤ 12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) := by
          exact mul_le_mul_of_nonneg_left hVolume (by norm_num)
        _ < ((2 ^ r : Nat) : ℝ) := hKernelMargin
    exact_mod_cast hReal
  have hKernel : 12 * (volume * 2 ^ (Delta - r)) < 2 ^ Delta := by
    calc
      12 * (volume * 2 ^ (Delta - r)) =
          (12 * volume) * 2 ^ (Delta - r) := by ring
      _ < 2 ^ r * 2 ^ (Delta - r) :=
        Nat.mul_lt_mul_of_pos_right hKernelSmall (by positivity)
      _ = 2 ^ Delta := by
        rw [← pow_add]
        congr 1
        omega
  exact ⟨hRank, hGenerator, hKernel⟩
private theorem simultaneousDistance_twelvefold_real_margins_of_entropy_gaps
    (rho delta : ℝ) (Delta : Nat) (hRhoNonnegative : 0 ≤ rho)
    (hGeneratorGap :
      Real.log 12 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ))
    (hKernelGap :
      Real.log 12 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    12 * (((2 ^ randomRowCount rho Delta : Nat) : ℝ) *
      Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
        ((2 ^ Delta : Nat) : ℝ) ∧
      12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        ((2 ^ randomRowCount rho Delta : Nat) : ℝ) := by
  let r := randomRowCount rho Delta
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRows : (r : ℝ) ≤ rho * Delta :=
    randomRowCount_cast_le hRhoNonnegative
  have hRowsLog := mul_le_mul_of_nonneg_right hRows hlog.le
  have hFloor : rho * Delta < (r : ℝ) + 1 :=
    randomRowCount_lt_add_one rho Delta
  have hFloorLog := mul_lt_mul_of_pos_right hFloor hlog
  have hGeneratorExponent :
      Real.log 12 +
          ((r : ℝ) * Real.log 2 +
            (Delta : ℝ) * Real.binEntropy delta) <
        (Delta : ℝ) * Real.log 2 := by
    nlinarith [hGeneratorGap, hRowsLog]
  have hKernelExponent :
      Real.log 12 + (Delta : ℝ) * Real.binEntropy delta <
        (r : ℝ) * Real.log 2 := by
    nlinarith [hKernelGap, hFloorLog]
  have hPow (k : Nat) :
      ((2 ^ k : Nat) : ℝ) =
        Real.exp ((k : ℝ) * Real.log 2) := by
    calc
      ((2 ^ k : Nat) : ℝ) = (2 : ℝ) ^ k := by norm_cast
      _ = (Real.exp (Real.log (2 : ℝ))) ^ k := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((k : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log (2 : ℝ)) k).symm
  constructor
  · change 12 * (((2 ^ r : Nat) : ℝ) *
        Real.exp ((Delta : ℝ) * Real.binEntropy delta)) <
      ((2 ^ Delta : Nat) : ℝ)
    calc
      12 * (((2 ^ r : Nat) : ℝ) *
          Real.exp ((Delta : ℝ) * Real.binEntropy delta)) =
          Real.exp (Real.log 12 +
            ((r : ℝ) * Real.log 2 +
              (Delta : ℝ) * Real.binEntropy delta)) := by
        rw [Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 12), ← hPow r]
      _ < Real.exp ((Delta : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hGeneratorExponent
      _ = ((2 ^ Delta : Nat) : ℝ) := (hPow Delta).symm
  · change 12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
      ((2 ^ r : Nat) : ℝ)
    calc
      12 * Real.exp ((Delta : ℝ) * Real.binEntropy delta) =
          Real.exp (Real.log 12 +
            (Delta : ℝ) * Real.binEntropy delta) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 12)]
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hKernelExponent
      _ = ((2 ^ r : Nat) : ℝ) := (hPow r).symm
private theorem exists_eventual_simultaneousDistance_twelvefold_entropy_margins
    (rho delta : ℝ) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      Real.log 12 <
          ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) ∧
        Real.log 12 + Real.log 2 <
          (rho * Real.log 2 - Real.binEntropy delta) *
            (Delta : ℝ) := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hRhoLog : rho * Real.log 2 < (1 / 2 : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hRhoHalf hlog
  have hGeneratorSlope :
      0 < (1 - rho) * Real.log 2 - Real.binEntropy delta := by
    nlinarith [hEntropy, hRhoLog]
  have hKernelSlope :
      0 < rho * Real.log 2 - Real.binEntropy delta := by
    linarith
  obtain ⟨generatorThreshold, hGeneratorThreshold⟩ :=
    exists_nat_gt
      (Real.log 12 /
        ((1 - rho) * Real.log 2 - Real.binEntropy delta))
  obtain ⟨kernelThreshold, hKernelThreshold⟩ :=
    exists_nat_gt
      ((Real.log 12 + Real.log 2) /
        (rho * Real.log 2 - Real.binEntropy delta))
  refine ⟨max generatorThreshold kernelThreshold, ?_⟩
  intro Delta hThreshold
  have hGeneratorLe : generatorThreshold ≤ Delta :=
    (Nat.le_max_left _ _).trans hThreshold
  have hKernelLe : kernelThreshold ≤ Delta :=
    (Nat.le_max_right _ _).trans hThreshold
  have hGeneratorCast :
      (generatorThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hGeneratorLe
  have hKernelCast :
      (kernelThreshold : ℝ) ≤ Delta := by
    exact_mod_cast hKernelLe
  have hGeneratorAtThreshold :
      Real.log 12 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) *
          (generatorThreshold : ℝ) := by
    have h := (div_lt_iff₀ hGeneratorSlope).mp hGeneratorThreshold
    nlinarith [h]
  have hKernelAtThreshold :
      Real.log 12 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) *
          (kernelThreshold : ℝ) := by
    have h := (div_lt_iff₀ hKernelSlope).mp hKernelThreshold
    nlinarith [h]
  constructor
  · have hScaled :=
      mul_le_mul_of_nonneg_left hGeneratorCast hGeneratorSlope.le
    nlinarith [hGeneratorAtThreshold, hScaled]
  · have hScaled :=
      mul_le_mul_of_nonneg_left hKernelCast hKernelSlope.le
    nlinarith [hKernelAtThreshold, hScaled]
private theorem simultaneousDistance_twice_count_bound_of_twelvefold_components
    {r Delta distance : Nat} (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hRank : 12 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      12 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      12 * ((∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
        2 ^ (Delta - r)) < 2 ^ Delta) :
    2 * distanceFailureCountBound r Delta distance <
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  have hDeltaLe : Delta ≤ r * Delta := by
    calc
      Delta = 1 * Delta := by omega
      _ ≤ r * Delta := Nat.mul_le_mul_right Delta hr
  have hSplitDelta :
      2 ^ (r * Delta) = 2 ^ (r * Delta - Delta) * 2 ^ Delta := by
    rw [← pow_add, Nat.sub_add_cancel hDeltaLe]
  have hSplitR :
      2 ^ (r * Delta - r) =
        2 ^ (r * Delta - Delta) * 2 ^ (Delta - r) := by
    rw [← pow_add]
    congr 1
    omega
  let volume := ∑ weight ∈ Finset.range distance, Nat.choose Delta weight
  let common := 2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)
  have hcommon : 0 < common := by dsimp [common]; positivity
  have hball :
      2 * (2 * (2 ^ r - 1) + 2 * ((2 ^ r - 1) * volume) +
        2 * (volume * 2 ^ (Delta - r))) < 2 ^ Delta := by
    dsimp [volume]
    omega
  change 2 * (2 * (2 ^ r - 1) * common +
    2 * (((2 ^ r - 1) * volume) * common) +
    2 * (volume * (2 ^ (r * Delta) * 2 ^ (r * Delta - r)))) < _
  calc
    2 * (2 * (2 ^ r - 1) * common +
        2 * (((2 ^ r - 1) * volume) * common) +
        2 * (volume * (2 ^ (r * Delta) * 2 ^ (r * Delta - r)))) =
      (2 * (2 * (2 ^ r - 1) + 2 * ((2 ^ r - 1) * volume) +
        2 * (volume * 2 ^ (Delta - r)))) * common := by
      rw [hSplitR]
      ring
    _ < 2 ^ Delta * common :=
      Nat.mul_lt_mul_of_pos_right hball hcommon
    _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by
      dsimp [common]
      calc
        2 ^ Delta * (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) =
          (2 ^ (r * Delta - Delta) * 2 ^ Delta) * 2 ^ (r * Delta) := by ring
        _ = 2 ^ (r * Delta) * 2 ^ (r * Delta) := by rw [← hSplitDelta]
private theorem exists_eventual_simultaneousDistance_twice_count_bound
    (rho delta : ℝ) (hRhoPositive : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ Delta : Nat, threshold ≤ Delta →
      let r := randomRowCount rho Delta
      let distance := Nat.ceil (delta * Delta)
      2 * distanceFailureCountBound r Delta distance <
        2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  obtain ⟨baseThreshold, hBase⟩ :=
    exists_eventual_simultaneousDistance_parameters
      rho delta hRhoPositive hRhoHalf hdeltaPositive hEntropy
  obtain ⟨marginThreshold, hMargin⟩ :=
    exists_eventual_simultaneousDistance_twelvefold_entropy_margins
      rho delta hRhoHalf hEntropy
  refine ⟨max baseThreshold marginThreshold, ?_⟩
  intro Delta hThreshold
  obtain ⟨hDelta, hr, hrDelta, hCeil, _, _⟩ :=
    hBase Delta ((Nat.le_max_left _ _).trans hThreshold)
  obtain ⟨hGeneratorGap, hKernelGap⟩ :=
    hMargin Delta ((Nat.le_max_right _ _).trans hThreshold)
  obtain ⟨hGeneratorMargin, hKernelMargin⟩ :=
    simultaneousDistance_twelvefold_real_margins_of_entropy_gaps
      rho delta Delta hRhoPositive.le hGeneratorGap hKernelGap
  obtain ⟨hRank, hGenerator, hKernel⟩ :=
    simultaneousDistance_twelvefold_bounds_of_real_margins
      Delta (randomRowCount rho Delta) (Nat.ceil (delta * Delta)) delta
      hDelta hrDelta.le (by omega) hdeltaPositive hdeltaHalf rfl hCeil
      hGeneratorMargin hKernelMargin
  exact simultaneousDistance_twice_count_bound_of_twelvefold_components
    hr hrDelta.le hRank hGenerator hKernel
private theorem nat_card_event_eq_card_eventFinset
    {Ω : Type u} [Fintype Ω] (event : Ω → Prop) :
    Nat.card {sample : Ω // event sample} = (eventFinset event).card := by
  rw [Nat.card_eq_fintype_card, eventFinset, Fintype.card_subtype]
private theorem card_distanceGoodPunctureFailure_antitone
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    {distance distance' : Nat} (hDistance : distance ≤ distance')
    (w q : Nat) (dualSide : Bool) :
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance' w q dualSide sample} ≤
    Nat.card {sample : RandomLocalCodeSample r A B //
      distanceGoodPunctureFailure distance w q dualSide sample} := by
  apply nat_card_event_le_of_imp
  intro sample h
  obtain ⟨hA, hB, hADual, hBDual, hFailure⟩ := h
  exact ⟨fun word hw hn => hDistance.trans (hA word hw hn),
    fun word hw hn => hDistance.trans (hB word hw hn),
    fun word hw hn => hDistance.trans (hADual word hw hn),
    fun word hw hn => hDistance.trans (hBDual word hw hn), hFailure⟩
private theorem hasPositiveUniformProbability_goodLocalCodeEvent_of_half_quarter_bounds
    {r Delta distance distance' w q : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hDistance : distance ≤ distance')
    (hHalf : 2 * distanceFailureCountBound r Delta distance' <
      2 ^ (r * Delta) * 2 ^ (r * Delta))
    (hQuarter : 4 * (∑ dualSide : Bool,
      Nat.card {sample : RandomLocalCodeSample r A B //
        distanceGoodPunctureFailure distance w q dualSide sample}) ≤
      Nat.card (RandomLocalCodeSample r A B)) :
    HasPositiveUniformProbability
      (GoodLocalCodeEvent (r := r) (A := A) (B := B)
        r (Delta - r) distance' w q) := by
  apply hasPositiveUniformProbability_goodLocalCodeEvent_of_count_bound hA hB
  have hBase := sum_card_simultaneousDistanceBad_le
    (r := r) (distance := distance') hA hB
  change (∑ index : SimultaneousDistanceBadIndex r distance' A B,
    (eventFinset (simultaneousDistanceBad index)).card) ≤
      distanceFailureCountBound r Delta distance' at hBase
  have hRobust :
      (∑ dualSide : Bool,
        Nat.card {sample : RandomLocalCodeSample r A B //
          distanceGoodPunctureFailure distance' w q dualSide sample}) ≤
      (∑ dualSide : Bool,
        Nat.card {sample : RandomLocalCodeSample r A B //
          distanceGoodPunctureFailure distance w q dualSide sample}) := by
    apply Finset.sum_le_sum
    intro dualSide _
    exact card_distanceGoodPunctureFailure_antitone hDistance w q dualSide
  rw [← card_randomLocalCodeSample hA hB] at hHalf
  simp_rw [nat_card_event_eq_card_eventFinset] at hQuarter hRobust
  rw [Nat.card_eq_fintype_card] at hQuarter
  rw [Fintype.sum_sum_type]
  change (∑ index : SimultaneousDistanceBadIndex r distance' A B,
      (eventFinset (simultaneousDistanceBad index)).card) +
    (∑ dualSide : Bool,
      (eventFinset (distanceGoodPunctureFailure distance' w q dualSide)).card) <
        Fintype.card (RandomLocalCodeSample r A B)
  omega
private theorem exists_eventual_source_goodLocalCodeEvent_positive
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          HasPositiveUniformProbability
            (GoodLocalCodeEvent (r := randomRowCount rho n) (A := A) (B := B)
              (randomRowCount rho n) (n - randomRowCount rho n)
              (Nat.ceil (delta * n))
              (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon)))
              (Nat.floor ((n : ℝ) ^ gamma))) := by
  obtain ⟨tH, htH⟩ := exists_eventual_simultaneousDistance_twice_count_bound
    rho delta hRho hRhoHalf hDelta hDeltaHalf hEntropy
  obtain ⟨tQ, htQ⟩ := exists_eventual_source_conditionedRobustness_quarter
    epsilon gamma delta rho hEpsilon hEpsilonUpper hGamma hDelta hRho
  refine ⟨max tH tQ, ?_⟩
  intro n hn A B _ _ hA hB
  exact hasPositiveUniformProbability_goodLocalCodeEvent_of_half_quarter_bounds
    hA hB (Nat.floor_le_ceil (delta * n))
    (htH n ((Nat.le_max_left _ _).trans hn))
    (htQ n ((Nat.le_max_right _ _).trans hn) A B hA hB)
namespace ChainComplexData
end ChainComplexData
namespace LeftRightCayleySquareComplex
end LeftRightCayleySquareComplex
namespace RawData
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
end RawData
namespace Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
variable [DecidableEq Square]
end Data
namespace Family
variable {Index : Type u}
variable {G A B Square XBasis ZBasis : Index → Type v}
variable [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable [∀ i, Fintype (Square i)] [∀ i, DecidableEq (Square i)]
variable [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
end Family
end QEC.Coding.QuantumTanner
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2)
    (_hGammaLower : 1 / 2 + epsilon < gamma) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          ∃ sample : RandomLocalCodeSample (randomRowCount rho n) A B,
            GoodLocalCodeEvent
              (randomRowCount rho n) (n - randomRowCount rho n)
              (Nat.ceil (delta * n))
              (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
              (Nat.floor ((n : ℝ) ^ gamma)) sample := by
  obtain ⟨threshold, hThreshold⟩ := exists_eventual_source_goodLocalCodeEvent_positive
    (epsilon / 2) gamma delta rho (by linarith) (by linarith)
    hGamma hDelta hDeltaHalf hRho hRhoHalf hEntropy
  refine ⟨threshold, ?_⟩
  intro n hn A B _ _ hA hB
  exact (hasPositiveUniformProbability_iff_exists _).mp
    (hThreshold n hn A B hA hB)
end QEC.Coding.QuantumTanner
