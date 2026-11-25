-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_lineIndex_smul_f78a06c73a31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:47.569802+00:00
-- url     : https://prove2.me/submissions/1db9e823-2461-47a6-81ff-4f0047e59a11

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution {h : HermitianForm F E W} {La : AddSubgroup W} {γ : h.unitaryGroup}
    (hγ : γ • La = La) (x : W) : lineIndex E La (γ • x) = lineIndex E La x := by
  let f : W →+ W := ((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom
  have hf : Function.Injective f := (γ : W ≃ₗ[E] W).injective
  have hfx : ∀ y : W, f y = γ • y := fun y => rfl
  have h1 : (ringMultiples E x).map f = ringMultiples E (γ • x) := by
    rw [ringMultiples, ringMultiples, ← AddMonoidHom.range_comp]
    congr 1
    ext a
    simp only [AddMonoidHom.comp_apply, hfx]
    simp [Subgroup.smul_def, LinearEquiv.smul_def]
  have h2 : La.map f = La := by
    conv_rhs => rw [← hγ]
    change La.map f = (γ : W ≃ₗ[E] W) • La
    rw [AddSubgroup.pointwise_smul_def]
    rfl
  have h3 : ((Submodule.span E {x}).toAddSubgroup).map f =
      (Submodule.span E {γ • x}).toAddSubgroup := by
    ext y
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [hfx, smul_comm]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c • x, ⟨c, rfl⟩, by rw [hfx, smul_comm]⟩
  unfold lineIndex
  conv_rhs => rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  rw [AddSubgroup.map_inf_eq _ _ f hf, h1, h2, h3]
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
