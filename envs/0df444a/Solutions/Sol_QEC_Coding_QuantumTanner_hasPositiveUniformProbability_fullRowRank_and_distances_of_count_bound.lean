-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_fullRowRank_and_distances_of_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:38:24.764614+00:00
-- url     : https://prove2.me/submissions/772a8752-c4a6-470c-8500-e3475380d482

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
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_iff_exists
import Theorems.Thm_QEC_Coding_QuantumTanner_card_binaryLowWeightWords
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_rowCombination_lowWeight_of_not_codeA_distance
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_rankFailureWitness_of_not_fullRowRank
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_lowWeight_kernel_of_not_codeB_distance
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
      2 * (2 ^ r - 1) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
          2 * (((2 ^ r - 1) *
              (∑ weight ∈ Finset.range distance,
                Nat.choose Delta weight)) *
            (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) *
            (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
  rw [hasPositiveUniformProbability_iff_exists]
  by_contra hnoGood
  have hnoGood' : ∀ sample : RandomLocalCodeSample r A B,
      ¬(sample.HasFullRowRank ∧
        HasMinimumDistanceAtLeast sample.codeA distance ∧
        HasMinimumDistanceAtLeast sample.codeB distance ∧
        HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
        HasMinimumDistanceAtLeast sample.codeB.dual distance) := by
    intro sample hsample
    exact hnoGood ⟨sample, hsample⟩
  let badUnion : Finset (RandomLocalCodeSample r A B) :=
    Finset.univ.biUnion fun index :
      SimultaneousDistanceBadIndex r distance A B =>
        eventFinset (simultaneousDistanceBad index)
  have hsubset :
      (Finset.univ : Finset (RandomLocalCodeSample r A B)) ⊆ badUnion := by
    intro sample _hsample
    obtain ⟨index, hindex⟩ :=
      simultaneousDistanceBad_covers sample (hnoGood' sample)
    exact Finset.mem_biUnion.mpr
      ⟨index, Finset.mem_univ index,
        (mem_eventFinset (simultaneousDistanceBad index) sample).mpr hindex⟩
  have hspaceLeUnion :
      Fintype.card (RandomLocalCodeSample r A B) ≤ badUnion.card := by
    simpa only [Finset.card_univ] using Finset.card_le_card hsubset
  have hUnionLeSum : badUnion.card ≤
      ∑ index : SimultaneousDistanceBadIndex r distance A B,
        (eventFinset (simultaneousDistanceBad index)).card := by
    exact Finset.card_biUnion_le
  have hsumLt :
      (∑ index : SimultaneousDistanceBadIndex r distance A B,
        (eventFinset (simultaneousDistanceBad index)).card) <
          Fintype.card (RandomLocalCodeSample r A B) := by
    rw [card_randomLocalCodeSample hA hB]
    exact (sum_card_simultaneousDistanceBad_le hA hB).trans_lt hcount
  exact (not_lt_of_ge (hspaceLeUnion.trans hUnionLeSum)) hsumLt
end QEC.Coding.QuantumTanner
