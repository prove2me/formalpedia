-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_eq_unipMat_8f17e87357aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:20.957884+00:00
-- url     : https://prove2.me/submissions/a71d46a2-4495-44e1-bb7a-2b852c27e1ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCoordProper
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
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
theorem _root_.solution {H G : Matrix ι ι ℂ} {X W₀ : ι → ℂ} (hU : Gᴴ * H * G = H)
    (hX : G *ᵥ X = X) (hz : ∀ z, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, G *ᵥ z = z + c • X)
    (hXW : star X ⬝ᵥ (H *ᵥ W₀) = 1) (hWX : star W₀ ⬝ᵥ (H *ᵥ X) = 1) :
    G = unipMat H X W₀ (G *ᵥ W₀ - W₀) := by
  have ip : ∀ a b, star (G *ᵥ a) ⬝ᵥ (H *ᵥ (G *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hU]
  set u := G *ᵥ W₀ - W₀ with hu
  have huX : star u ⬝ᵥ (H *ᵥ X) = 0 := by
    have := ip W₀ X
    rw [hX] at this
    simp only [hu, star_sub, sub_dotProduct, this, sub_self]
  have key : ∀ e, G *ᵥ e = unipVec H X W₀ u e := by
    intro e
    set b := star X ⬝ᵥ (H *ᵥ e) with hb
    set z := e - b • W₀ with hzdef
    have hXz : star X ⬝ᵥ (H *ᵥ z) = 0 := by
      simp only [hzdef, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hXW, smul_eq_mul,
        mul_one, b, sub_self]
    obtain ⟨c, hc⟩ := hz z hXz
    have hGW : G *ᵥ W₀ = W₀ + u := by rw [hu]; abel
    have hc' : c = -(star u ⬝ᵥ (H *ᵥ z)) := by
      have := ip W₀ z
      rw [hc, hGW] at this
      simp only [star_add, add_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
        hWX, huX, smul_eq_mul] at this
      linear_combination this
    have he : e = z + b • W₀ := by rw [hzdef]; abel
    have : G *ᵥ e = z + c • X + b • (W₀ + u) := by
      rw [he, mulVec_add, mulVec_smul, hc, hGW]
    rw [this, hc']
    simp only [unipVec, ← hb, ← hzdef]
    rw [he]
    simp only [smul_add, neg_smul]
    abel
  ext i j
  rw [unipMat, of_apply, ← key, mulVec_single_one, col_apply]
end GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
