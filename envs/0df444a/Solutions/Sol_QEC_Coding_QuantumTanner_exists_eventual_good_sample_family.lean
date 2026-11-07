-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_good_sample_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:40:44.33179+00:00
-- url     : https://prove2.me/submissions/508acbcf-597e-441e-a25d-93206d7a71dd

import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_cofinal_blockLength_of_group_card
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_distance_ge_of_hasParameters
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_localityProfile
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_good_sample_parameters
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
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hDeltaHalf : delta < 1 / 2)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho Delta) A B,
        ∀ (Index : Type u) (G : Index → Type v)
          [∀ i, Group (G i)] [∀ i, Fintype (G i)]
          (L : ∀ i, A → G i) (R : ∀ i, B → G i)
          (invA : Equiv.Perm A) (invB : Equiv.Perm B)
          (hL : ∀ i, Function.Injective (L i)) (hR : ∀ i, Function.Injective (R i))
          (hLA : ∀ i a, L i (invA a) = (L i a)⁻¹)
          (hRB : ∀ i b, R i (invB b) = (R i b)⁻¹)
          (hTNC : ∀ i g a b, L i a * g ≠ g * R i b),
        (∀ i, HasMeanZeroBilinearBound
          (cayleySquareComplex (L i) (R i) invA invB (hL i) (hR i) (hLA i) (hRB i)
            (hTNC i)).leftCayleyGraph (2 * Real.sqrt (Delta : ℝ))) →
        (∀ i, HasMeanZeroBilinearBound
          (cayleySquareComplex (L i) (R i) invA invB (hL i) (hR i) (hLA i) (hRB i)
            (hTNC i)).rightCayleyGraph (2 * Real.sqrt (Delta : ℝ))) →
        (∀ N : Nat, ∃ i, N ≤ Fintype.card (G i)) →
        HasGoodSampleFamily L R invA invB hL hR hLA hRB hTNC
          delta epsilon rho Delta sample := by
  obtain ⟨t, ht⟩ := exists_eventual_good_sample_parameters
    delta epsilon gamma rho hDeltaDistance hDeltaHalf hEpsilon hEpsilonHalf
    hGammaLower hGammaUpper hRho hRhoHalf hEntropy
  refine ⟨max t 1, ?_⟩
  intro Delta hLarge A B _ _ hCardA hCardB
  have hDegree : 0 < Delta := by
    have := (Nat.le_max_right t 1).trans hLarge
    omega
  obtain ⟨sample, _hGood, hSample⟩ := ht Delta
    ((Nat.le_max_left _ _).trans hLarge) A B hCardA hCardB
  refine ⟨sample, ?_⟩
  intro Index G _ _ L R invA invB hL hR hLA hRB hTNC hLeft hRight hGroups
  unfold HasGoodSampleFamily
  let family := fun i => canonicalDataOfLocalCodeSample (L i) (R i) invA invB
    (hL i) (hR i) (hLA i) (hRB i) (hTNC i) sample
  have hCofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength :=
    Family.cofinal_blockLength_of_group_card family Delta hDegree
      (fun _ => hCardA) (fun _ => hCardB) hGroups
  have hFinite (i : Index) := hSample (G i) (L i) (R i) invA invB
    (hL i) (hR i) (hLA i) (hRB i) (hTNC i) (hLeft i) (hRight i)
  let distance : Index → Nat := fun i => Classical.choose (hFinite i).2.2
  have hBounds (i : Index) := Classical.choose_spec (hFinite i).2.2
  have hParameters (i : Index) :
      (family i).HasParameters (family i).blockLength (family i).encodedDimension (distance i) :=
    (hBounds i).1
  have hRate : QEC.QLDPC.HasEventualRateAtLeast (Family.ofData family hCofinal)
      ((1 - 2 * rho) ^ 2) := by
    refine ⟨0, fun i _ => ?_⟩
    exact (hBounds i).2.1
  have hDistancePointwise (i : Index) :
      delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) *
          ((Family.ofData family hCofinal).blockLength i : ℝ) ≤
        ((Family.ofData family hCofinal).distance i : ℝ) := by
    have hSemantic := Family.ofData_distance_ge_of_hasParameters family hCofinal i (hParameters i)
    have hBound := (hBounds i).2.2.1
    have hBoundReal : delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) *
        (family i).blockLength ≤ (distance i : ℝ) := by
      simpa only [div_mul_eq_mul_div] using hBound
    exact hBoundReal.trans (by exact_mod_cast hSemantic)
  have hDistance : QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (Family.ofData family hCofinal)
      (delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon))) :=
    ⟨0, fun i _ => hDistancePointwise i⟩
  have hLocalityPointwise (i : Index) :
      QEC.Coding.BoundedLocality ((Family.ofData family hCofinal).localityProfile i)
        (Delta * Delta) := by
    rw [Family.ofData_localityProfile]
    exact (hBounds i).2.2.2
  have hLocality : QEC.QLDPC.HasUniformLDPC (Family.ofData family hCofinal) :=
    ⟨Delta * Delta, hLocalityPointwise⟩
  have hRatePositive : 0 < (1 - 2 * rho) ^ 2 := sq_pos_of_pos (by linarith)
  have hDistancePositive : 0 < delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) := by
    apply div_pos hDeltaDistance
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hDegree) _)
  exact ⟨hCofinal, ⟨hLocality, ⟨_, hRatePositive, hRate⟩,
    ⟨_, hDistancePositive, hDistance⟩⟩, hRate, hDistance,
    fun i => ⟨(hBounds i).2.1, hDistancePointwise i, hLocalityPointwise i⟩⟩
end QEC.Coding.QuantumTanner
