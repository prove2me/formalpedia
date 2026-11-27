-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerCovolumeFinite_proof_f9484ef5d1d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:10.625104+00:00
-- url     : https://prove2.me/submissions/6ac8766b-3ba7-4f91-868f-517bfe65b793

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_covering_of_relIndex_ne_zero_7d0986eea57f
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementForm_proof_bdb227fda16c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_DiscreteFundamentalDomain_proof_acd672081314
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WittPartner_proof_a6df1f660009
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0
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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace StabilizerCovolumeFinite
theorem _root_.solution [FiniteDimensional E W] (h : HermitianForm F E W)
    (v : Basis ι E W) (h₁ : CovolumeFiniteBelow.{u} F E (finrank E W))
    (h₂ : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (h₃ : StabilizerLevi.Statement h v) (h₄ : UnipotentModulus.Statement h v)
    (h₅ : UnipotentCocompact.Statement h v) (h₆ : CongruenceLift.Statement h) :
    StabilizerCovolumeFinite.Statement h v := by
  classical
  intro D La x₀ hLa hx₀ hne hiso ν hν

  obtain ⟨w₀, hxw, hww⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨h', hh'⟩ := ComplementForm.proof h x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  have hlt : finrank E (hypComplement h x₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : w₀ ∈ hypComplement h x₀ w₀ := htop ▸ Submodule.mem_top
    rw [mem_hypComplement, hxw] at hmem
    exact one_ne_zero hmem.1

  obtain ⟨i, q, hi, hq, hqi, hker, hiw, hcompat⟩ := h₃ x₀ w₀ hp h' hh' _ v'

  obtain ⟨D', La', G'', hLa', hG'', hidx, hlift⟩ := h₆ D La x₀ w₀ hLa hx₀ hp h' hh'
  let μL : Measure (archUnitary h' v') := Measure.haar
  obtain ⟨FD', hFD', hFD'fin⟩ :=
    h₁ (hypComplement h x₀ w₀) h' _ v' hlt μL D' La' hLa'
  obtain ⟨T, hTm, hTfin, hT⟩ := exists_covering_of_relIndex_ne_zero μL (archEmbed h' v') G''
    (latticeStab h' La') hidx FD' hFD' hFD'fin
  set Γ := (vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀) with hΓ
  have hcovL : ∀ l, ∃ γ ∈ Γ, q γ * l ∈ T := by
    intro l
    obtain ⟨m, hm, hml⟩ := hT l
    obtain ⟨γ₀, hγx, hγw, hγm⟩ := ComplementExtension.proof h x₀ w₀ hp h' hh' m
    have hγ₀ : γ₀ ∈ latticeStab h La := hlift m hm γ₀ hγx hγw hγm
    refine ⟨i (archEmbed h' v' m), ?_, by rw [hqi]; exact hml⟩
    rw [hΓ, Subgroup.mem_subgroupOf, hcompat γ₀ m hγx hγw hγm]
    exact ⟨⟨γ₀, hγ₀⟩, hγx, rfl⟩

  obtain ⟨C, hC, hcovN⟩ := h₅ D La x₀ hLa hx₀ hne hiso
  let j : unipRadical h v x₀ →* vecFixGroup h v x₀ :=
    Subgroup.inclusion (unipRadical_le_vecFixGroup h v x₀)
  have hjc : Continuous j := (continuous_subtype_val.subtype_mk _)
  have hj : IsClosedEmbedding j := by
    refine ⟨IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩
    have : Set.range j = Subtype.val ⁻¹' (unipRadical h v x₀ : Set (archUnitary h v)) := by
      ext g
      exact ⟨by rintro ⟨n, rfl⟩; exact n.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    rw [this]
    exact (isClosed_unipRadical h v x₀).preimage continuous_subtype_val
  have hjr : ∀ g, q g = 1 ↔ g ∈ j.range := fun g => (hker g).trans
    ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩
  let μN : Measure (unipRadical h v x₀) := Measure.haar
  have hemb : MeasurableEmbedding (Subtype.val : vecFixGroup h v x₀ → archUnitary h v) :=
    (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.measurableEmbedding
  have hconj : ∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j := by
    intro l
    have key := h₄ x₀ w₀ hp μN ((i l : vecFixGroup h v x₀) : archUnitary h v) ⟨(i l).2, hiw l⟩
    have hf : Continuous fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹ :=
      (continuous_const.mul hjc).mul continuous_const
    rw [← hemb.comap_map (μN.map _), ← hemb.comap_map (μN.map j),
      Measure.map_map hemb.measurable hf.measurable,
      Measure.map_map hemb.measurable hjc.measurable]
    have e1 : (Subtype.val ∘ fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹) =
        fun n : unipRadical h v x₀ =>
          ((i l : vecFixGroup h v x₀) : archUnitary h v) * (n : archUnitary h v) *
            ((i l : vecFixGroup h v x₀) : archUnitary h v)⁻¹ := by
      funext n
      simp [j]
    have e2 : (Subtype.val ∘ j) = (Subtype.val : unipRadical h v x₀ → archUnitary h v) := by
      funext n
      rfl
    rw [e1, e2, key]
  have hcovN' : ∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C := fun n => by
    obtain ⟨δ, hδ, hδn⟩ := hcovN n
    exact ⟨δ, hδ, hδn⟩

  obtain ⟨S, -, hSfin, hScov⟩ :=
    h₂ x₀ w₀ h' _ v' i q j hi hq hj hqi hjr μL μN hconj Γ C T hC hTm hTfin hcovN' hcovL ν

  have hdG : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨((x : vecFixGroup h v x₀) : archUnitary h v), x.2⟩ :
        vecStabGroup h v La x₀))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨FD, -, hFD⟩ := DiscreteFundamentalDomain.proof (vecFixGroup h v x₀) ν Γ hdisc

  have hle : ν FD ≤ ν S := by
    rw [hFD.measure_eq_tsum S]
    refine (measure_mono fun x hx => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, hγx⟩ := hScov x
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγx
  have hν0 : ν ≠ 0 := fun h0 => (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) (by simp [h0])
  exact ⟨FD, hFD, pos_iff_ne_zero.2 (hFD.measure_ne_zero hν0), hle.trans_lt hSfin⟩
end StabilizerCovolumeFinite
end GroundTheory.Heights₂.Heights.FiniteCovolume
