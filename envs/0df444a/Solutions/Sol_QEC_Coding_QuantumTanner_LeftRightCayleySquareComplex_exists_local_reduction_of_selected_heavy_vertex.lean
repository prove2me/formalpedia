-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_reduction_of_selected_heavy_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:20:15.762556+00:00
-- url     : https://prove2.me/submissions/fd389801-63e1-4bbd-bad9-adef8b274229

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_punctured_approximations_of_normal_neighbors
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_balanced_nonexceptional_neighbor_punctures
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_cutoff_mul_incoming_heavyDegree_le_twice_localWeight
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_punctured_minimumDistance
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensor_weight_reduction_of_punctured_approximation
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
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w p : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hCard : Fintype.card A = Fintype.card B) (hp : p ≤ Fintype.card A)
    (hpA : p < dA) (hpB : p < dB)
    (hRobust : IsRobustWithPunctureResistance CA CB w p)
    (hBudget : 2 * w ≤ (dA - p) * (dB - p))
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (normal exceptional : Finset G) (g : G) (threshold : ℝ)
    (hHeavy : threshold ≤ (∑ h ∈ normal, X.heavyUnionGraph side x cutoff h g : Nat))
    (hBad : (∑ h ∈ exceptional, X.unionCayleyGraph h g) ≤ p)
    (rowError columnError : Nat)
    (hCovers : ∀ h ∉ exceptional, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (h, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (h, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      rows.card ≤ columnError ∧ columns.card ≤ rowError)
    (hErrors : Fintype.card B * columnError + Fintype.card A * rowError ≤ w)
    (hMargin : (3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
      (cutoff : ℝ) * threshold) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, !side) x + c) <
        HammingWeight (X.localRestriction (g, !side) x) := by
  obtain ⟨removedA, removedB, hEqual, hSizeA, hLeft, hRight⟩ :=
    X.exists_balanced_nonexceptional_neighbor_punctures g exceptional p hCard hp hBad
  have hSizeB : removedB.card ≤ p := hEqual ▸ hSizeA
  have hLowerA : HasMinimumDistanceAtLeast CA dA := hA.choose_spec.2.2.2
  have hLowerB : HasMinimumDistanceAtLeast CB dB := hB.choose_spec.2.2.2
  obtain ⟨dA', hMinA', hDistanceA⟩ :=
    exists_punctured_minimumDistance CA dA hA removedA (hSizeA.trans_lt hpA)
  obtain ⟨dB', hMinB', hDistanceB⟩ :=
    exists_punctured_minimumDistance CB dB hB removedB (hSizeB.trans_lt hpB)
  have hBudget' : 2 * w ≤ dA' * dB' := by
    have hDA : dA - p ≤ dA' := (by omega : dA - p ≤ dA - removedA.card).trans hDistanceA
    have hDB : dB - p ≤ dB' := (by omega : dB - p ≤ dB - removedB.card).trans hDistanceB
    exact hBudget.trans (Nat.mul_le_mul hDA hDB)
  obtain ⟨C, R, hC, hR, hCError, hRError⟩ :=
    X.exists_punctured_approximations_of_normal_neighbors hX CA CB dA dB hLowerA hLowerB
      x g (!side) removedA removedB rowError columnError
      (fun a => by
        obtain ⟨rows, columns, hLocal, hCover, hRows, hColumns, hRow, hColumn⟩ :=
          hCovers _ (hLeft a)
        exact ⟨rows, columns, by simpa only [Bool.not_not] using hLocal,
          by simpa only [Bool.not_not] using hCover, hRows, hColumns, hColumn⟩)
      (fun b => by
        obtain ⟨rows, columns, hLocal, hCover, hRows, hColumns, hRow, hColumn⟩ :=
          hCovers _ (hRight b)
        exact ⟨rows, columns, by simpa only [Bool.not_not] using hLocal,
          by simpa only [Bool.not_not] using hCover, hRows, hColumns, hRow⟩)
  have hWeight := X.cutoff_mul_incoming_heavyDegree_le_twice_localWeight
    hX side x cutoff normal g
  have hRealWeight : (cutoff : ℝ) * threshold ≤
      (2 * HammingWeight (X.localRestriction (g, !side) x) : Nat) := by
    have hScaled := mul_le_mul_of_nonneg_left hHeavy (Nat.cast_nonneg cutoff)
    have hWeight' : ((cutoff * (∑ h ∈ normal, X.heavyUnionGraph side x cutoff h g) : Nat) : ℝ) ≤
        (2 * HammingWeight (X.localRestriction (g, !side) x) : Nat) := by exact_mod_cast hWeight
    simp only [Nat.cast_mul] at hWeight'
    simpa only [Nat.cast_mul] using hScaled.trans hWeight'
  have hNatMargin : 3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (p * Fintype.card B + Fintype.card A * p) <
      2 * HammingWeight (X.localRestriction (g, !side) x) := by
    exact_mod_cast hMargin.trans_le hRealWeight
  have hLoss : removedA.card * Fintype.card B + Fintype.card A * removedB.card ≤
      p * Fintype.card B + Fintype.card A * p :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hSizeA) (Nat.mul_le_mul_left _ hSizeB)
  apply exists_tensor_weight_reduction_of_punctured_approximation CA CB removedA removedB
    dA' dB' w hMinA' hMinB' (hRobust removedA removedB hEqual hSizeA) hBudget'
    (X.localRestriction (g, !side) x) C R hC hR
  · omega
  · omega
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
