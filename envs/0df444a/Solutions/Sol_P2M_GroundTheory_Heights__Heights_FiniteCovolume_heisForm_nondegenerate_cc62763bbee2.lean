-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_nondegenerate_cc62763bbee2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:08.391863+00:00
-- url     : https://prove2.me/submissions/9c3055ec-959d-4a6c-8f29-0aed9dd796de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_comm_f10b979213d4
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_hForm_9f2691cc4673
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_right_6b8edb0e313a
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hp : IsHyperbolicPair h x₀ w₀) :
    (heisForm h v x₀ w₀).Nondegenerate := by
  classical
  have left : ∀ y : heisY h v x₀ w₀, (∀ z, heisForm h v x₀ w₀ y z = 0) → y = 0 := by
    intro y hy
    apply Subtype.ext
    funext w
    change (y : InfinitePlace E → ι → ℂ) w = 0
    obtain ⟨hH, hd, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
    have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
      rw [← hForm_conj hH, hab, map_one]
    apply eq_zero_of_hForm hd
    intro z
    set q := z - hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w -
      hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w with hq
    have hqa : hForm (gramAt h v w) (vecAt v x₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, ha, hab]
      ring
    have hqb : hForm (gramAt h v w) (vecAt v w₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, hb, hba]
      ring
    have key : ∀ c : ℂ, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (c • q)).re = 0 := by
      intro c
      have hmem : (Pi.single w (c • q) : InfinitePlace E → ι → ℂ) ∈ heisY h v x₀ w₀ := by
        intro w'
        by_cases hw : w' = w
        · subst hw
          simp only [Pi.single_eq_same, hForm_smul_right, hqa, hqb, mul_zero, and_self]
        · simp only [Pi.single_eq_of_ne hw, hForm_zero_right, and_self]
      have := hy ⟨_, hmem⟩
      rw [heisForm_apply, Finset.sum_eq_single w] at this
      · simpa using this
      · intro w' _ hw
        simp [Pi.single_eq_of_ne hw, hForm_zero_right]
      · simp
    have h1 := key 1
    have h2 := key Complex.I
    rw [hForm_smul_right, one_mul] at h1
    rw [hForm_smul_right, Complex.I_mul_re, neg_eq_zero] at h2
    have hyq : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) q = 0 := Complex.ext h1 h2
    have hya : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v x₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).1, map_zero]
    have hyb : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).2, map_zero]
    have hz : z = q + hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w +
        hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w := by
      rw [hq]
      abel
    rw [hz, hForm_add_right, hForm_add_right, hForm_smul_right, hForm_smul_right, hyq, hya, hyb]
    ring
  exact ⟨left, fun y hy => left y fun z => by rw [heisForm_comm hp]; exact hy z⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume
