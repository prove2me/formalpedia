-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_weight_bounded_decomposition_of_half_distance_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:03:43.481684+00:00
-- url     : https://prove2.me/submissions/4a5740d6-fe2f-403d-b694-cdf5ce7e7005

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
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      HammingWeight rowPart ≤ HammingWeight x ∧
      HammingWeight columnPart ≤ HammingWeight x := by
  obtain ⟨r, c, hr, hc, hParts, hRowSupport, hColumnSupport⟩ :=
    exists_supported_dualTensor_decomposition CA CB distanceA distanceB
      hDistanceA hDistanceB x hx rows columns (by omega) (by omega) hCovered
  have hWeights := hammingWeight_parts_le_of_supported_decomposition
    CA CB distanceA distanceB hDistanceA hDistanceB r c hr hc rows columns
      hRows hColumns hRowSupport hColumnSupport
  rw [← hParts] at hWeights
  exact ⟨r, c, hr, hc, hParts, hWeights.1, hWeights.2⟩
end QEC.Coding.QuantumTanner
