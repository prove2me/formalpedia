-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_hasPositiveUniformProbability_fullRowRank_and_distances
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:39:00.11121+00:00
-- url     : https://prove2.me/submissions/8aca0945-1adf-4428-bb9e-65a23c7d20dc

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
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_degree
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
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
    (rho delta : ℝ) (hRhoPositive : 0 < rho)
    (hRhoHalf : rho < 1 / 2) (hdeltaPositive : 0 < delta)
    (hdeltaHalf : delta < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ (Delta : Nat), threshold ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = Delta → Fintype.card B = Delta →
          HasPositiveUniformProbability
            (fun sample :
                RandomLocalCodeSample (randomRowCount rho Delta) A B =>
              sample.HasFullRowRank ∧
                HasMinimumDistanceAtLeast sample.codeA
                  (Nat.ceil (delta * Delta)) ∧
                HasMinimumDistanceAtLeast sample.codeB
                  (Nat.ceil (delta * Delta)) ∧
                HasMinimumDistanceAtLeast sample.codeA.dual
                  (Nat.ceil (delta * Delta)) ∧
                HasMinimumDistanceAtLeast sample.codeB.dual
                  (Nat.ceil (delta * Delta))) := by
  obtain ⟨threshold, hThreshold⟩ :=
    exists_eventual_simultaneousDistance_parameters
      rho delta hRhoPositive hRhoHalf hdeltaPositive hEntropy
  refine ⟨threshold, ?_⟩
  intro Delta hDegree A B _ _ hA hB
  obtain ⟨hDelta, hRows, hRowsDelta, hceil,
    hGeneratorGap, hKernelGap⟩ := hThreshold Delta hDegree
  exact hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
    rho delta hA hB hRhoPositive.le hDelta hRows hRowsDelta.le
    hdeltaPositive hdeltaHalf hceil hGeneratorGap hKernelGap
end QEC.Coding.QuantumTanner
