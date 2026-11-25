-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_EigenReflectionMaps_proof_a091c329dbe0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:57.280407+00:00
-- url     : https://prove2.me/submissions/08d57554-6988-41dc-b460-393b9c68fc6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflectionMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_dotProduct_mulVec_of_isHermitian_f0205efbd7ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_unit_mul_star_eq_norm_2958366fd685
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_mul_conj
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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ι)
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace EigenReflectionMaps
theorem _root_.solution (h₁ : EigenReflection.Statement ι)
    (h₂ : EigenspacesOrthogonal.Statement ι) : EigenReflectionMaps.Statement ι := by
  intro H P hMaj ε hε a a' ha ha' hρ
  have hPh : P.IsHermitian := hMaj.1.isHermitian
  obtain ⟨α, hα1, hαs, hαs'⟩ := exists_unit_mul_star_eq_norm (star a ⬝ᵥ (P *ᵥ a'))
  refine ⟨α, hα1, ?_⟩
  set v : ι → ℂ := a' - α • a with hv
  by_cases hv0 : v = 0
  · refine ⟨1, by simp, by simp, ?_, fun u _ => by simp⟩
    rw [one_mulVec]
    exact sub_eq_zero.mp hv0
  have hAv : majInvolution H P *ᵥ v = ε • v := by
    rw [hv, mulVec_sub, mulVec_smul, ha, ha', smul_sub, smul_comm]
  obtain ⟨hRP, hRH, hRv, hRfix⟩ := h₁ H P hMaj ε hε v hv0 hAv
  refine ⟨pReflection P v, hRP, hRH, ?_, ?_⟩
  ·
    have hconj : star a' ⬝ᵥ (P *ᵥ a) = star (star a ⬝ᵥ (P *ᵥ a')) :=
      (star_dotProduct_mulVec_of_isHermitian hPh a' a).symm
    have hαα : star α * α = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα1]; simp
    have hw : star v ⬝ᵥ (P *ᵥ (a' + α • a)) = 0 := by
      rw [hv, star_sub, star_smul, mulVec_add, mulVec_smul, sub_dotProduct, dotProduct_add,
        dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        hconj, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← hρ]
      have e1 : star α * (α * (star a ⬝ᵥ (P *ᵥ a))) = (star α * α) * (star a ⬝ᵥ (P *ᵥ a)) := by
        ring
      rw [e1, hαα, hαs, hαs']
      ring
    have hRw := hRfix _ hw
    have hsplit : a' = (1 / 2 : ℂ) • (a' + α • a) + (1 / 2 : ℂ) • v := by
      rw [hv]; ext i; simp; ring
    rw [hsplit, mulVec_add, mulVec_smul, mulVec_smul, hRw, hRv, hv]
    ext i; simp; ring
  · intro u hu
    apply hRfix
    rcases hε with rfl | rfl
    · have h := h₂ H P hMaj v u (by rw [hAv, one_smul]) (by rw [hu, neg_smul, one_smul])
      exact h
    · have h := h₂ H P hMaj u v (by rw [hu, neg_neg, one_smul]) (by rw [hAv, neg_smul, one_smul])
      rw [← star_dotProduct_mulVec_of_isHermitian hPh, h, star_zero]
end EigenReflectionMaps
end GroundTheory.Heights₂.Heights.FiniteCovolume
