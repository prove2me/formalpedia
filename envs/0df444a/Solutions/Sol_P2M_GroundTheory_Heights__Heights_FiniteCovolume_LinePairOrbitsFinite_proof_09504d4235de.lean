-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:25:13.994548+00:00
-- url     : https://prove2.me/submissions/31d6d231-38db-409d-832c-6efd538d2f0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275
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
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
universe u
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace LinePairOrbitsFinite
theorem _root_.solution (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (h₂ : WittPartner.Statement h)
    (h₃ : ComplementForm.Statement h) (h₄ : ComplementExtension.Statement h)
    (h₅ : AdaptedReduction.Statement h) : LinePairOrbitsFinite.Statement h := by
  intro D
  by_cases hex : ∃ v₀ : W, v₀ ≠ 0 ∧ h.toSesq v₀ v₀ = 0
  swap
  · refine ⟨∅, Set.finite_empty, fun La l _ hl => ?_⟩
    exfalso
    have hne : l ≠ ⊥ := fun hb => by
      have := hl.1
      rw [hb, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨x, hxl, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact hex ⟨x, hx0, hl.2 x hxl x hxl⟩
  obtain ⟨v₀, hv₀, hv₀₀⟩ := hex
  obtain ⟨w₀, hvw, hww⟩ := h₂ v₀ hv₀ hv₀₀
  have hp : IsHyperbolicPair h v₀ w₀ := ⟨hv₀₀, hww, hvw⟩
  obtain ⟨h', hh'⟩ := h₃ v₀ w₀ hp
  obtain ⟨KK, hKK, n, D', hn, hred⟩ := h₅ v₀ w₀ hp h' hh' D
  have hdim : finrank E (hypComplement h v₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hv : v₀ ∈ hypComplement h v₀ w₀ := htop ▸ Submodule.mem_top
    have h1 : h.toSesq w₀ v₀ = 1 := by
      rw [← h.isSymm.eq v₀ w₀, hvw, map_one]
    exact one_ne_zero (h1 ▸ (mem_hypComplement.1 hv).2)
  obtain ⟨S', hS', hS'L⟩ := h₁ (hypComplement h v₀ w₀) h' hdim D'
  have : NoZeroSMulDivisors ℕ W := ⟨fun {c x} hcx => by
    rw [← Nat.cast_smul_eq_nsmul E] at hcx
    rcases smul_eq_zero.1 hcx with h0 | h0
    · exact Or.inl (Nat.cast_eq_zero.1 h0)
    · exact Or.inr h0⟩
  let Mof : AddSubgroup E × AddSubgroup E → AddSubgroup (hypComplement h v₀ w₀) →
      AddSubgroup W := fun p L =>
    p.1.map ((smulAddHom E W).flip v₀) ⊔ L.map (hypComplement h v₀ w₀).subtype.toAddMonoidHom ⊔
      p.2.map ((smulAddHom E W).flip w₀)
  refine ⟨(⋃ p ∈ KK, ⋃ L ∈ S', {La | Mof p L ≤ La ∧ (∀ x ∈ La, n • x ∈ Mof p L) ∧ La.FG}) ×ˢ
    {Submodule.span E {v₀}},
    (hKK.biUnion fun p _ => hS'.biUnion fun L _ => finite_sandwich _ hn).prod
      (Set.finite_singleton _), ?_⟩
  intro La l hLa hl
  obtain ⟨g, La₁, hgLa, hgv, hK, hsplit, hInt⟩ := hred La l hLa hl
  obtain ⟨L, hL, m, hmL⟩ := hS'L _ hInt
  obtain ⟨gm, hgv₀, hgw₀, hgx⟩ := h₄ v₀ w₀ hp h' hh' m

  have hsmul : ∀ (γ : h.unitaryGroup) (c : E) (x : W), γ • (c • x) = c • (γ • x) := fun γ c x =>
    map_smul (γ : W ≃ₗ[E] W) c x
  have hmem : ∀ x : W, x ∈ gm⁻¹ • La₁ ↔ gm • x ∈ La₁ := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
      simpa using hy
    · intro hx
      have := AddSubgroup.smul_mem_pointwise_smul _ gm⁻¹ La₁ hx
      rw [inv_smul_smul] at this
      exact this
  refine ⟨(gm⁻¹ • La₁, Submodule.span E {v₀}), ⟨?_, rfl⟩, g * gm, ?_, ?_⟩
  · refine Set.mem_iUnion₂.2 ⟨_, hK, Set.mem_iUnion₂.2 ⟨L, hL, ?_, ?_, ?_⟩⟩
    · refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [hmem]
        change gm • (a • v₀) ∈ La₁
        rw [hsmul, hgv₀]
        exact ha
      · rintro _ ⟨y, hy, rfl⟩
        rw [hmem]
        change gm • (y : W) ∈ La₁
        rw [hgx]
        have : m • y ∈ m • L := AddSubgroup.smul_mem_pointwise_smul y m L hy
        rw [hmL] at this
        exact this
      · rintro _ ⟨b, hb, rfl⟩
        rw [hmem]
        change gm • (b • w₀) ∈ La₁
        rw [hsmul, hgw₀]
        exact hb
    · intro x hx
      rw [hmem] at hx
      obtain ⟨a, ha, b, hb, hz⟩ := hsplit _ hx
      set z : W := n • (gm • x) - a • v₀ - b • w₀ with hzdef
      have hzL : z ∈ La₁ :=
        La₁.sub_mem (La₁.sub_mem (La₁.nsmul_mem hx n) ha) hb
      have hz' : (⟨z, hz⟩ : hypComplement h v₀ w₀) ∈ m • L := by
        rw [hmL]
        exact hzL
      obtain ⟨y, hy, hyz⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hz'
      have hnx : n • x = a • v₀ + (y : W) + b • w₀ := by
        apply (MulAction.injective gm)
        show gm • (n • x) = gm • (a • v₀ + (y : W) + b • w₀)
        have e1 : gm • (n • x) = n • (gm • x) := map_nsmul (gm : W ≃ₗ[E] W) n x
        have e2 : gm • (y : W) = z := by
          rw [hgx, hyz]
        rw [e1, smul_add, smul_add, hsmul, hsmul, hgv₀, hgw₀, e2, hzdef]
        abel
      rw [hnx]
      refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left ⟨a, ha, rfl⟩)
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right ⟨y, hy, rfl⟩)
      · exact AddSubgroup.mem_sup_right ⟨b, hb, rfl⟩
    · have hLa₁ : La₁ = g⁻¹ • La := by
        rw [← hgLa, inv_smul_smul]
      have hfg : ∀ (γ : h.unitaryGroup) (S : AddSubgroup W), S.FG → (γ • S).FG := by
        intro γ S hS
        have : γ • S = S.map (((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom) := by
          ext x
          constructor
          · intro hx
            obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
            exact ⟨y, hy, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact AddSubgroup.smul_mem_pointwise_smul y γ S hy
        rw [this]
        exact fg_map_of_fg hS _
      exact hfg _ _ (hLa₁ ▸ hfg _ _ hLa.isLattice.fg)
  · rw [mul_smul, smul_inv_smul, hgLa]
  · have hgv0 : (g : W ≃ₗ[E] W) v₀ ≠ 0 := fun h0 =>
      hv₀ ((g : W ≃ₗ[E] W).map_eq_zero_iff.1 h0)
    have hg' : ((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀ = (g : W ≃ₗ[E] W) v₀ := by
      change (g : W ≃ₗ[E] W) ((gm : W ≃ₗ[E] W) v₀) = _
      exact congrArg _ hgv₀
    change (Submodule.span E {v₀}).map _ = l
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span E {((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀} = l
    rw [hg']
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hgv
    · rw [finrank_span_singleton hgv0, hl.1]
end LinePairOrbitsFinite
end GroundTheory.Heights₂.Heights.FiniteCovolume
