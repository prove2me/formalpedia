-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_proof_92693f740236
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:15.297424+00:00
-- url     : https://prove2.me/submissions/96f2924f-6ea1-4f9b-8081-dd3424714256

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHyperbolicPairTransitive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_carry_1fda0d326aee
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
theorem _root_.solution (h : HermitianForm F E W) [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h := by
  intro v w v' w' ⟨hv, hw, hvw⟩ ⟨hv', hw', hvw'⟩
  have hwv : h.toSesq w v = 1 := by rw [sesq_swap h v w, hvw, map_one]
  have hwv' : h.toSesq w' v' = 1 := by rw [sesq_swap h v' w', hvw', map_one]
  have ee : ∀ a b : W, h.toSesq a a = 0 → h.toSesq b b = 0 → h.toSesq a b = 1 →
      h.toSesq b a = 1 → h.toSesq (a + b) (a + b) = 2 ∧ h.toSesq (a - b) (a - b) = -2 ∧
        h.toSesq (a - b) (a + b) = 0 := by
    intro a b ha hb hab hba
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, ha, hb, hab, hba]
    norm_num
  obtain ⟨e1, f1, fe1⟩ := ee v w hv hw hvw hwv
  obtain ⟨e2, f2, fe2⟩ := ee v' w' hv' hw' hvw' hwv'
  have two : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨g₁, hg₁, -⟩ := exists_unitary_carry h (v + w) (v' + w') 0 (e1.trans e2.symm)
    (e1 ▸ two) (map_zero _) (map_zero _)
  have hf : h.toSesq ((g₁ : W ≃ₗ[E] W) (v - w)) (v' + w') = 0 := by
    rw [← hg₁, g₁.2, fe1]
  obtain ⟨g₂, hg₂, hc⟩ := exists_unitary_carry h ((g₁ : W ≃ₗ[E] W) (v - w)) (v' - w') (v' + w')
    (by rw [g₁.2, f1, f2]) (by rw [g₁.2, f1]; exact neg_ne_zero.2 two) hf fe2
  have key : ∀ z, (g₂ * g₁ : h.unitaryGroup) • z = (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) z) :=
    fun _ => rfl
  have hE : (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) (v + w)) = v' + w' := by rw [hg₁, hc]
  have hv2 : v = (2 : E)⁻¹ • ((v + w) + (v - w)) := by
    rw [add_add_sub_cancel, ← two_smul E v, smul_smul, inv_mul_cancel₀ two, one_smul]
  have hw2 : w = (2 : E)⁻¹ • ((v + w) - (v - w)) := by
    rw [add_sub_sub_cancel, ← two_smul E w, smul_smul, inv_mul_cancel₀ two, one_smul]
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [key, hv2, map_smul, map_smul, map_add, map_add, hE, hg₂, add_add_sub_cancel,
      ← two_smul E v', smul_smul, inv_mul_cancel₀ two, one_smul]
  · rw [key, hw2, map_smul, map_smul, map_sub, map_sub, hE, hg₂, add_sub_sub_cancel,
      ← two_smul E w', smul_smul, inv_mul_cancel₀ two, one_smul]
end GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
