-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementLattice_proof_1c65f8cd215a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:30.574794+00:00
-- url     : https://prove2.me/submissions/6292ae5d-164c-4a4f-b13b-4b5c570e8fda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isAddTorsionFree_of_module_706dda8260c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_fg_map_of_injective_f02305c255ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_factorial_nsmul_mem_of_mem_dual_793087957248
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ComplementLattice
theorem _root_.solution (h : HermitianForm F E W) [FiniteDimensional E W] :
    ComplementLattice.Statement h := by
  intro v₀ w₀ hvw h' hh' D n hn
  refine ⟨(D.factorial * n) ^ (finrank ℚ E * finrank E W), ?_⟩
  intro La hLa hdec
  set P : AddSubgroup (hypComplement h v₀ w₀) := La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom with hP
  obtain ⟨hvv, hww, hvw1⟩ := hvw
  have hwv1 : h.toSesq w₀ v₀ = 1 := by
    rw [← h.isSymm.eq v₀ w₀, hvw1, map_one]
  have hsymm0 : ∀ x y : W, h.toSesq x y = 0 → h.toSesq y x = 0 := fun x y hxy => by
    rw [← h.isSymm.eq x y, hxy, map_zero]
  have memP : ∀ x : (hypComplement h v₀ w₀), x ∈ P ↔ (x : W) ∈ La := fun x => Iff.rfl

  let π₀ : W →ₗ[E] W :=
    LinearMap.id - (h.toSesq w₀).smulRight v₀ - (h.toSesq v₀).smulRight w₀
  have hπ₀ : ∀ x, π₀ x = x - h.toSesq w₀ x • v₀ - h.toSesq v₀ x • w₀ := fun x => rfl
  have hπ₀mem : ∀ x, π₀ x ∈ (hypComplement h v₀ w₀) := by
    intro x
    rw [hπ₀, mem_hypComplement]
    constructor <;> simp only [map_sub, map_smul, smul_eq_mul, hvv, hww, hvw1, hwv1] <;> ring
  have hfix : ∀ y ∈ (hypComplement h v₀ w₀), π₀ y = y := fun y hy => by
    rw [mem_hypComplement] at hy
    rw [hπ₀, hy.1, hy.2]
    simp
  have hπv : π₀ v₀ = 0 := by
    rw [hπ₀, hwv1, hvv]
    simp
  have hπw : π₀ w₀ = 0 := by
    rw [hπ₀, hww, hvw1]
    simp

  have hz : ∀ x ∈ La, ∃ a b : E, a • v₀ ∈ La ∧ b • w₀ ∈ La ∧
      n • x - a • v₀ - b • w₀ ∈ (hypComplement h v₀ w₀) ∧ n • x - a • v₀ - b • w₀ ∈ La ∧
      n • π₀ x = n • x - a • v₀ - b • w₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hmem⟩ := hdec x hx
    change a • v₀ ∈ La at ha
    change b • w₀ ∈ La at hb
    refine ⟨a, b, ha, hb, hmem, La.sub_mem (La.sub_mem (La.nsmul_mem hx n) ha) hb, ?_⟩
    rw [← hfix _ hmem, map_sub, map_sub, map_nsmul, map_smul, map_smul, hπv, hπw]
    simp

  have hPlat : IsLattice E P := by
    refine ⟨fun a x hx => ?_, ?_, ?_⟩
    · rw [memP] at hx ⊢
      exact hLa.isLattice.smul_mem a _ hx
    · refine fg_of_fg_map_of_injective (hypComplement h v₀ w₀).subtype.toAddMonoidHom Subtype.val_injective ?_
      exact fg_of_le_fg (AddSubgroup.map_comap_le _ _) hLa.isLattice.fg
    · let π : W →ₗ[E] (hypComplement h v₀ w₀) := π₀.codRestrict (hypComplement h v₀ w₀) hπ₀mem
      have hrange : LinearMap.range π = ⊤ :=
        LinearMap.range_eq_top.2 fun y => ⟨y, Subtype.ext (hfix y y.2)⟩
      rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← hLa.isLattice.span_eq_top,
        Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, b, -, -, -, hzLa, hkey⟩ := hz x hx
      have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hnx : (n : E) • π x ∈ P := by
        rw [memP, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
        change n • π₀ x ∈ La
        rw [hkey]
        exact hzLa
      have : π x = (n : E)⁻¹ • ((n : E) • π x) := by
        rw [smul_smul, inv_mul_cancel₀ hnE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)

  have hPint : IsIntegralOn h' P := fun x hx y hy => by
    rw [hh']
    exact hLa.integral _ hx _ hy
  set N := D.factorial * n with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.factorial_pos D) hn
  set G := dualLattice h' P with hG
  have hPG : P ≤ G := fun x hx y hy => hPint x hx y hy

  have hNG : G.map (nsmulAddMonoidHom N) ≤ P := by
    rintro _ ⟨y', hy', rfl⟩
    have hdual : n • (y' : W) ∈ dualLattice h La := by
      intro x hx
      obtain ⟨a, b, -, -, hmem, hzLa, -⟩ := hz x hx
      have hy0 := (mem_hypComplement.1 y'.2)
      have e1 : h.toSesq (y' : W) v₀ = 0 := hsymm0 _ _ hy0.1
      have e2 : h.toSesq (y' : W) w₀ = 0 := hsymm0 _ _ hy0.2
      have hnx : n • x = (n • x - a • v₀ - b • w₀) + a • v₀ + b • w₀ := by abel
      have key : h.toSesq (n • (y' : W)) x = h.toSesq (y' : W) (n • x - a • v₀ - b • w₀) := by
        rw [map_nsmul, LinearMap.smul_apply, ← map_nsmul]
        conv_lhs => rw [hnx]
        rw [map_add, map_add, map_smul, map_smul, e1, e2]
        simp
      rw [key]
      have := hy' ⟨_, hmem⟩ hzLa
      rwa [hh'] at this
    have h2 := factorial_nsmul_mem_of_mem_dual hLa hdual
    rw [nsmulAddMonoidHom_apply, memP, Submodule.coe_smul_of_tower, hN, ← smul_smul]
    exact h2

  have : IsAddTorsionFree (hypComplement h v₀ w₀) := isAddTorsionFree_of_module E (hypComplement h v₀ w₀)
  have hGfg : G.FG := fg_of_fg_map_of_injective (nsmulAddMonoidHom N)
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hNpos.ne')
    (fg_of_le_fg hNG hPlat.fg)
  have : Module.Finite ℤ G.toIntSubmodule :=
    Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hGfg)
  have : Module.Finite ℤ G := inferInstanceAs (Module.Finite ℤ G.toIntSubmodule)
  have hrank : finrank ℤ G ≤ finrank ℚ E * finrank E W := by
    letI : Module ℚ W := Module.compHom W (algebraMap ℚ E)
    have : IsScalarTower ℚ E W := ⟨fun q e w => by
      change (q • e) • w = algebraMap ℚ E q • e • w
      rw [Algebra.smul_def, mul_smul]⟩
    have : Module.Finite ℚ W := Module.Finite.trans E W
    let b := Module.finBasis ℤ G
    let f : G →ₗ[ℤ] W := ((hypComplement h v₀ w₀).subtype.toAddMonoidHom.comp G.subtype).toIntLinearMap
    have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
    have hliZ : LinearIndependent ℤ (f ∘ b) :=
      b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
    have := hliQ.fintype_card_le_finrank
    rw [Fintype.card_fin, ← Module.finrank_mul_finrank ℚ E W] at this
    exact this
  have hidx : P.relIndex G ≤ N ^ finrank ℤ G := by
    rw [← AddSubgroup.relIndex_map_nsmul N G]
    refine AddSubgroup.relIndex_le_of_le_left hNG ?_
    rw [AddSubgroup.relIndex_map_nsmul]
    positivity
  refine ⟨hPlat, hPint, fun h0 => ?_, ?_⟩
  · have := AddSubgroup.relIndex_eq_zero_of_le_left hNG h0
    rw [AddSubgroup.relIndex_map_nsmul] at this
    exact (pow_ne_zero _ hNpos.ne') this
  · exact hidx.trans (Nat.pow_le_pow_right hNpos hrank)
end ComplementLattice
end GroundTheory.Heights₂.Heights.FiniteCovolume
