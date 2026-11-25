-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_carry_1fda0d326aee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:30.898742+00:00
-- url     : https://prove2.me/submissions/36731a07-604f-4ebb-81ea-42c314fc7a93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHyperbolicPairTransitive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_sub_smul_a1fa7a01f2b5
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
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
theorem _root_.solution (h : HermitianForm F E W) [FiniteDimensional E W] (x y c : W)
    (hxy : h.toSesq x x = h.toSesq y y) (hx : h.toSesq x x ≠ 0)
    (hxc : h.toSesq x c = 0) (hyc : h.toSesq y c = 0) :
    ∃ g : h.unitaryGroup, (g : W ≃ₗ[E] W) x = y ∧ (g : W ≃ₗ[E] W) c = c := by
  have hr : ∀ z, conj F E (h.toSesq z z) = h.toSesq z z := fun z => h.isSymm.eq z z
  have two : (2 : E) ≠ 0 := two_ne_zero
  by_cases hβ : h.toSesq (x - y) x = 0
  ·
    have hyx : h.toSesq y x = h.toSesq x x := by
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hβ
      exact hβ.symm
    obtain ⟨g₁, hg₁⟩ := exists_unitary_sub_smul h (x + y) (2 * h.toSesq x x)
      (mul_ne_zero two hx) (by
        simp only [map_add, LinearMap.add_apply, map_mul, map_ofNat, hr]
        rw [sesq_swap h y x, hyx, hr, ← hxy]; ring)
    obtain ⟨g₂, hg₂⟩ := exists_unitary_sub_smul h y (h.toSesq y y / 2)
      (div_ne_zero (hxy ▸ hx) two) (by rw [map_div₀, map_ofNat, hr]; ring)
    refine ⟨g₂ * g₁, ?_, ?_⟩
    · change (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) x) = y
      have e1 : (g₁ : W ≃ₗ[E] W) x = -y := by
        rw [hg₁, map_add, LinearMap.add_apply, hyx, ← two_mul, div_self (mul_ne_zero two hx),
          one_smul]
        abel
      have hy : h.toSesq y y ≠ 0 := hxy ▸ hx
      rw [e1, hg₂, map_neg, neg_div, neg_smul, sub_neg_eq_add,
        show h.toSesq y y / (h.toSesq y y / 2) = 2 by field_simp, two_smul]
      abel
    · change (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) c) = c
      rw [hg₁, map_add, LinearMap.add_apply, hxc, hyc, add_zero, zero_div, zero_smul, sub_zero,
        hg₂, hyc, zero_div, zero_smul, sub_zero]
  · obtain ⟨g, hg⟩ := exists_unitary_sub_smul h (x - y) (h.toSesq (x - y) x) hβ (by
      simp only [map_sub, LinearMap.sub_apply, hr]
      rw [sesq_swap h x y, hxy, conj_conj]; ring)
    refine ⟨g, ?_, ?_⟩
    · rw [hg, div_self hβ, one_smul, sub_sub_cancel]
    · rw [hg, map_sub, LinearMap.sub_apply, hxc, hyc, sub_zero, zero_div, zero_smul, sub_zero]
end GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
