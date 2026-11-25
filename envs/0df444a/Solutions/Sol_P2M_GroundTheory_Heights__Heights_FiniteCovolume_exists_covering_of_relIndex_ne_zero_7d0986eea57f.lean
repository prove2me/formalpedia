-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_covering_of_relIndex_ne_zero_7d0986eea57f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:52:07.272639+00:00
-- url     : https://prove2.me/submissions/085d024a-37d9-44d5-9ff3-03b608d9c234

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWittPartner
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDiscreteFundamentalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerCovolume
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {G K : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group K] (μ : Measure G) [μ.IsMulLeftInvariant] (f : K →* G)
    (A B : Subgroup K) (hidx : A.relIndex B ≠ 0) (FD : Set G)
    (hFD : IsFundamentalDomain (B.map f) FD μ) (hfin : μ FD < ⊤) :
    ∃ T : Set G, MeasurableSet T ∧ μ T < ⊤ ∧ ∀ l, ∃ a ∈ A, f a * l ∈ T := by
  classical
  have : (A.subgroupOf B).FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  set bad := {l : G | ¬ ∃ γ : B.map f, γ • l ∈ FD} with hbad_def
  have hbad : μ bad = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hFD.ae_covers.mono fun x hx hx' => hx' hx)
  refine ⟨(⋃ k : B ⧸ A.subgroupOf B, (fun x => f ((Quotient.out k : B) : K) * x) ⁻¹'
    toMeasurable μ FD) ∪ toMeasurable μ bad, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun k => (measurableSet_toMeasurable μ FD).preimage
      (measurable_const_mul _)).union (measurableSet_toMeasurable μ bad)
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [measure_toMeasurable, hbad, add_zero]
    refine lt_of_le_of_lt (measure_iUnion_fintype_le μ _) ?_
    simp only [measure_preimage_mul, measure_toMeasurable]
    exact ENNReal.sum_lt_top.2 fun _ _ => hfin
  · intro l
    by_cases hl : l ∈ bad
    · exact ⟨1, one_mem _, Or.inr (subset_toMeasurable μ bad (by simpa using hl))⟩
    · rw [hbad_def, Set.mem_ofPred_eq, not_not] at hl
      obtain ⟨⟨γ, hγ⟩, hγl⟩ := hl
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hγ
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
      set k : B ⧸ A.subgroupOf B := QuotientGroup.mk (⟨b, hb⟩ : B)
      have hcA : (((c : B) : K)) ∈ A := c.2
      refine ⟨((c : B) : K)⁻¹, inv_mem hcA, Or.inl (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      apply subset_toMeasurable
      have e : ((Quotient.out k : B) : K) = b * ((c : B) : K) := by
        rw [hc]; rfl
      simp only [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      simpa [Subgroup.smul_def] using hγl
end GroundTheory.Heights₂.Heights.FiniteCovolume
