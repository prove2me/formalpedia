-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_eventual_local_weight_reduction_of_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:27:13.290275+00:00
-- url     : https://prove2.me/submissions/c9e4cc8a-6425-427e-b2ae-8a09dfa58ee5

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_local_weight_reduction_of_finite_mixing
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_distance_mixing_scalar_budgets
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_distance_density_margin
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_distance_integer_margins
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
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
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
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



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square : Type v) [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square],
      ∀ (X : LeftRightCayleySquareComplex G A B Square), X.HasCayleyLinkIdentities →
      ∀ (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (dA dB : Nat),
      MinimumDistance CA dA → MinimumDistance CB dB →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust CA CB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance CA CB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
        (Nat.floor ((Delta : ℝ) ^ gamma)) →
      ∀ (side : Bool) (x : Word (ZMod 2) Square), x ≠ 0 →
      (∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier) →
      HasExpanderMixingBound (X.squareGraph side) (Delta * Delta) (4 * (Delta : ℝ)) →
      HasExpanderMixingBound X.unionCayleyGraph (Delta + Delta) (4 * Real.sqrt (Delta : ℝ)) →
      ((X.activeVerticesOnSide side x).card : ℝ) ≤
        Fintype.card G / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon)) →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
        HammingWeight (X.localRestriction (g, !side) x + c) <
          HammingWeight (X.localRestriction (g, !side) x) := by
  obtain ⟨tI, hI⟩ := exists_eventual_distance_integer_margins delta epsilon gamma
    hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  obtain ⟨tD, hD⟩ := exists_eventual_distance_density_margin delta epsilon hDeltaDistance hEpsilon
  refine ⟨max tI tD, ?_⟩
  intro Delta hDegree G A B Square _ _ _ _ _ X hX CA CB dA dB hA hB hDistanceA hDistanceB hCardA hCardB
    hRobust hPunctures side x hx hLocal hSquareMixing hUnionMixing hSmall
  obtain ⟨hTwo, hNormalPos, hNormalWeight, hpDegree, hpD, heD, hPunctureBudget,
    hErrorBudget, hMargin, hFractionHalf, hLower⟩ :=
    hI Delta ((Nat.le_max_left _ _).trans hDegree)
  obtain ⟨_, hDensity⟩ := hD Delta ((Nat.le_max_right _ _).trans hDegree)
  let d := Nat.ceil (delta * Delta)
  let e := distanceLineError delta epsilon Delta
  let p := Nat.floor ((Delta : ℝ) ^ gamma)
  let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
  let cutoff := distanceNormalCutoff epsilon Delta
  have hDPos : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hdA : d ≤ dA := Nat.ceil_le.mpr hDistanceA
  have hdB : d ≤ dB := Nat.ceil_le.mpr hDistanceB
  have hdPos : 0 < d := Nat.ceil_pos.mpr (by positivity)
  have hDivA : (cutoff - 1) / dA ≤ e := by
    apply (Nat.le_div_iff_mul_le hdPos).mpr
    exact (Nat.mul_le_mul_left _ hdA).trans (Nat.div_mul_le_self _ _)
  have hDivB : (cutoff - 1) / dB ≤ e := by
    apply (Nat.le_div_iff_mul_le hdPos).mpr
    exact (Nat.mul_le_mul_left _ hdB).trans (Nat.div_mul_le_self _ _)
  have hActualPunctureBudget : 2 * w ≤ (dA - p) * (dB - p) :=
    hPunctureBudget.trans (Nat.mul_le_mul (Nat.sub_le_sub_right hdA p)
      (Nat.sub_le_sub_right hdB p))
  have hActualErrorBudget : Fintype.card B * ((cutoff - 1) / dB) +
      Fintype.card A * ((cutoff - 1) / dA) ≤ w := by
    rw [hCardA, hCardB]
    calc
      Delta * ((cutoff - 1) / dB) + Delta * ((cutoff - 1) / dA) ≤
          Delta * e + Delta * e := Nat.add_le_add (Nat.mul_le_mul_left _ hDivB)
            (Nat.mul_le_mul_left _ hDivA)
      _ = 2 * Delta * e := by ring
      _ ≤ w := hErrorBudget
  obtain ⟨hSquareSmall, hFractionBudget, hUnionDensity, hRatioBudget,
    hAverageBudget, hMeanBudget, hSelectionBudget⟩ := distance_mixing_scalar_budgets
      delta epsilon Delta (X.activeVerticesOnSide side x).card (Fintype.card G) p
      hTwo hDeltaDistance hSmall heD hDensity hFractionHalf hLower
  have hActualMargin : (3 * (Fintype.card B * ((cutoff - 1) / dB) +
      Fintype.card A * ((cutoff - 1) / dA)) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
        ((d - e : Nat) : ℝ) * (delta ^ 2 * Delta / 256) := by
    have hNat : 3 * (Delta * ((cutoff - 1) / dB) + Delta * ((cutoff - 1) / dA)) +
        2 * (p * Delta + Delta * p) ≤ 6 * Delta * e + 4 * Delta * p := by
      have hSum := Nat.add_le_add (Nat.mul_le_mul_left Delta hDivB)
        (Nat.mul_le_mul_left Delta hDivA)
      nlinarith only [hSum]
    rw [hCardA, hCardB]
    have hReal : ((3 * (Delta * ((cutoff - 1) / dB) + Delta * ((cutoff - 1) / dA)) +
        2 * (p * Delta + Delta * p) : Nat) : ℝ) ≤ (6 * Delta * e + 4 * Delta * p : Nat) := by
      exact_mod_cast hNat
    exact hReal.trans_lt hMargin
  apply X.exists_local_weight_reduction_of_finite_mixing hX CA CB dA dB w p
    cutoff (d - e) hA hB (hCardA.trans hCardB.symm) (by omega)
    (by simpa only [hCardA] using hpDegree) (hpD.trans_le hdA) (hpD.trans_le hdB)
    hRobust hPunctures hActualPunctureBudget hNormalPos hNormalWeight
    (hDivB.trans_lt (heD.trans_le hdA)) (hDivA.trans_lt (heD.trans_le hdB))
    (by omega) (by omega) hActualErrorBudget side x hx hLocal
    (4 * Delta) (4 * Real.sqrt (Delta : ℝ)) ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon))
    (delta * Delta / 2) (64 / (Delta : ℝ) ^ (1 - 2 * epsilon))
    (64 / (delta ^ 2 * Delta)) (32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon))
    (delta ^ 2 * Delta / 256)
    (by positivity) (by positivity) (Real.rpow_pos_of_pos hDPos _)
    (Nat.le_ceil _) (by positivity) (by positivity) hFractionHalf (by positivity)
    (by simpa only [hCardA, hCardB] using hSquareMixing)
    (by simpa only [hCardA, hCardB] using hUnionMixing)
    (by simpa only [hCardA, hCardB] using hSquareSmall) hFractionBudget
    (by simpa only [hCardA, hCardB] using hUnionDensity) hRatioBudget hAverageBudget
    (by simpa only [hCardA, hCardB] using hMeanBudget)
    (by simpa only [hCardA, hCardB] using hSelectionBudget) hActualMargin
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
