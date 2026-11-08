-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeB_distance_of_entropy_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:38:40.704226+00:00
-- url     : https://prove2.me/submissions/73c1b18a-3dbd-40a1-af74-50f5650de071

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
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_add_one
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_codeB_distance_of_count_bound
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
end RobustnessAsymptotics
section RobustnessIndexBounds
open Filter
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
private theorem exp_binEntropy_lt_pow_two_randomRowCount
    (rho delta : ℝ) (Delta : Nat)
    (hmargin : Real.log 2 <
      (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
      (2 : ℝ) ^ randomRowCount rho Delta := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hfloor := randomRowCount_lt_add_one rho Delta
  have hfloorLog := mul_lt_mul_of_pos_right hfloor hlog
  have hlt :
      (Delta : ℝ) * Real.binEntropy delta <
        (randomRowCount rho Delta : ℝ) * Real.log 2 := by
    nlinarith [hmargin, hfloorLog]
  calc
    Real.exp ((Delta : ℝ) * Real.binEntropy delta) <
        Real.exp ((randomRowCount rho Delta : ℝ) * Real.log 2) :=
          Real.exp_lt_exp.mpr hlt
    _ = (Real.exp (Real.log (2 : ℝ))) ^ randomRowCount rho Delta :=
      Real.exp_nat_mul (Real.log (2 : ℝ)) (randomRowCount rho Delta)
    _ = (2 : ℝ) ^ randomRowCount rho Delta := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
private theorem secondDistanceBad_count_bound_of_ball_lt
    {r Delta distance : Nat} (hDelta : 0 < Delta)
    (hball :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) < 2 ^ r) :
    (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
        (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) <
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by
  have hrle : r ≤ r * Delta := by
    simpa using Nat.mul_le_mul_left r hDelta
  have hscaled :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          2 ^ (r * Delta - r) < 2 ^ (r * Delta) := by
    calc
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          2 ^ (r * Delta - r) <
          2 ^ r * 2 ^ (r * Delta - r) :=
        Nat.mul_lt_mul_of_pos_right hball (pow_pos (by omega) _)
      _ = 2 ^ (r * Delta) := by
        rw [← pow_add]
        congr 1
        omega
  calc
    (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
        (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) =
        2 ^ (r * Delta) *
          ((∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
            2 ^ (r * Delta - r)) := by ring
    _ < 2 ^ (r * Delta) * 2 ^ (r * Delta) :=
      Nat.mul_lt_mul_of_pos_left hscaled (pow_pos (by omega) _)
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
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta) (hDelta : 0 < Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hmargin : Real.log 2 <
      (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        HasMinimumDistanceAtLeast sample.codeB
          (Nat.ceil (delta * Delta))) := by
  have hballReal := binaryHammingBall_le_exp_binEntropy_ceilRadius
    Delta delta hDelta hdeltaPositive hdeltaHalf hceil
  have hpowReal := exp_binEntropy_lt_pow_two_randomRowCount
    rho delta Delta hmargin
  have hball :
      (∑ weight ∈ Finset.range (Nat.ceil (delta * Delta)),
        Nat.choose Delta weight) <
        2 ^ randomRowCount rho Delta := by
    exact_mod_cast hballReal.trans_lt hpowReal
  exact hasPositiveUniformProbability_codeB_distance_of_count_bound
    hA hB (secondDistanceBad_count_bound_of_ball_lt hDelta hball)
end QEC.Coding.QuantumTanner
