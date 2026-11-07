-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SimplicialChain.boundedLocality_of_coface_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:04.909485+00:00
-- url     : https://prove2.me/submissions/92d0e9d9-c710-4ef4-9d84-55190c1ab266

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_card_facets
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_HammingWeight_boundary_canonicalBasis_eq_card_facets
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
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
namespace QEC.Coding.HighDimensionalExpander.SimplicialChain
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace Face
variable {K : AbstractSimplicialComplex V} {p : Nat}
end Face
variable (K : AbstractSimplicialComplex V)
private theorem canonicalBasisWord_eq_single
    {I : Type u} [DecidableEq I] (i : I) :
    canonicalBasisWord (F := ZMod 2) i = Pi.single i 1 := by
  classical
  ext i'
  by_cases hi : i = i'
  · subst i'
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, hi]
private theorem matrixToLin_canonicalBasis
    {Row Col : Type u} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col (ZMod 2)) (c : Col) :
    Matrix.toLin' M (canonicalBasisWord (F := ZMod 2) c) =
      fun r => M r c := by
  rw [canonicalBasisWord_eq_single]
  ext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc']
  · simp
private theorem wordLinearMapTranspose_matrixToLin_canonicalBasis
    {Row Col : Type u} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col (ZMod 2)) (r : Row) :
    wordLinearMapTranspose (Matrix.toLin' M)
        (canonicalBasisWord (F := ZMod 2) r) =
      fun c => M r c := by
  rw [canonicalBasisWord_eq_single]
  ext c
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single r]
  · simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      simp [hc']
    · simp
  · intro r' hr'
    simp [hr']
private theorem HammingWeight_sum_elim
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B]
    (x : Word F A) (y : Word F B) :
    HammingWeight (Sum.elim x y) =
      HammingWeight x + HammingWeight y := by
  classical
  let e :
      {s : Sum A B // Sum.elim x y s ≠ 0} ≃
        Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0} :=
    { toFun := fun s =>
        match s with
        | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
        | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, hb⟩
      invFun := fun s =>
        match s with
        | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
      left_inv := by rintro ⟨a | b, h⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  calc
    HammingWeight (Sum.elim x y) =
        Fintype.card {s : Sum A B // Sum.elim x y s ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card (Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0}) :=
      Fintype.card_congr e
    _ = HammingWeight x + HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
private theorem variableSupport_card_eq_boundary_columns
    (p : Nat) (τ : Face K (p + 1)) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence (chainComplexAt K p)).variableSupport τ).card =
      HammingWeight
          (boundary K p (canonicalBasisWord (F := ZMod 2) τ)) +
        HammingWeight
          (wordLinearMapTranspose (boundary K (p + 1))
            (canonicalBasisWord (F := ZMod 2) τ)) := by
  classical
  let x := boundary K p (canonicalBasisWord (F := ZMod 2) τ)
  let z := wordLinearMapTranspose (boundary K (p + 1))
    (canonicalBasisWord (F := ZMod 2) τ)
  have hSupport :
      (QEC.QLDPC.chainComplexBoundaryIncidence
          (chainComplexAt K p)).variableSupport τ =
        hammingSupport (Sum.elim x z) := by
    ext c
    rw [QEC.QLDPC.CheckIncidence.mem_variableSupport]
    simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases c with
    | inl σ =>
        dsimp [QEC.QLDPC.chainComplexBoundaryIncidence, chainComplexAt, x]
        simp only [boundary]
        rw [wordLinearMapTranspose_matrixToLin_canonicalBasis,
          matrixToLin_canonicalBasis]
    | inr υ =>
        dsimp [QEC.QLDPC.chainComplexBoundaryIncidence, chainComplexAt, z]
        simp only [boundary]
        rw [matrixToLin_canonicalBasis,
          wordLinearMapTranspose_matrixToLin_canonicalBasis]
  rw [hSupport]
  change HammingWeight (Sum.elim x z) =
    HammingWeight x + HammingWeight z
  exact HammingWeight_sum_elim x z
end QEC.Coding.HighDimensionalExpander.SimplicialChain
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SimplicialChain
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)
namespace QEC.Coding.HighDimensionalExpander.SimplicialChain
theorem _root_.solution
    (p B : Nat) (hp : 1 ≤ p)
    (hLower : ∀ σ : Face K p, (cofaces K p σ).card ≤ B)
    (hMiddle : ∀ τ : Face K (p + 1),
      (cofaces K (p + 1) τ).card ≤ B) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplexAt K p)).localityProfile
      (max (max B (p + 2)) (p + 1 + B)) := by
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
    (chainComplexAt K p)
  · intro σ
    change HammingWeight
      (wordLinearMapTranspose (boundary K p)
        (canonicalBasisWord (F := ZMod 2) σ)) ≤ _
    rw [HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces]
    exact (hLower σ).trans (Nat.le_max_left _ _)
  · intro υ
    change HammingWeight
      (boundary K (p + 1)
        (canonicalBasisWord (F := ZMod 2) υ)) ≤ _
    rw [HammingWeight_boundary_canonicalBasis_eq_card_facets,
      card_facets K (p + 1) (by omega)]
    exact Nat.le_max_right _ _
  · intro τ
    rw [variableSupport_card_eq_boundary_columns,
      HammingWeight_boundary_canonicalBasis_eq_card_facets,
      HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces,
      card_facets K p hp]
    exact Nat.add_le_add_left (hMiddle τ) (p + 1)
end QEC.Coding.HighDimensionalExpander.SimplicialChain
