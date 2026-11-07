-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeB_distance_of_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:37:56.435485+00:00
-- url     : https://prove2.me/submissions/518cb00f-3aff-4842-b129-6946fb0d536d

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
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_of_union_bound
import Theorems.Thm_QEC_Coding_QuantumTanner_card_binaryLowWeightWords
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_lowWeight_kernel_of_not_codeB_distance
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
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeB distance) := by
  apply hasPositiveUniformProbability_of_union_bound
    (J := {target : BinaryLowWeightWords B distance // target.1 ≠ 0})
    (bad := secondDistanceBad (r := r) (A := A))
  · exact secondDistanceBad_covers_not_codeB_distance
  · rw [card_randomLocalCodeSample hA hB]
    exact (sum_card_secondDistanceBad_le hA hB).trans_lt hcount
end QEC.Coding.QuantumTanner
