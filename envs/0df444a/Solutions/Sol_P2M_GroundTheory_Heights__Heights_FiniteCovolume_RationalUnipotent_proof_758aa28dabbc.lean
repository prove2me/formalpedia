-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_proof_758aa28dabbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:50.26863+00:00
-- url     : https://prove2.me/submissions/cbbe906f-929a-4130-ba87-85d94fd2e728

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_smul_98c1f23872d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_inv_smul_c1eaf2eb5e18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipMap_mem_c41bae6a48c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_conj_mem_integralClosure_3d6754791d38
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
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open RationalUnipotent
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace RationalUnipotent
theorem _root_.solution (h : HermitianForm F E W) : RationalUnipotent.Statement h := by
  intro D La x₀ w₀ hD hx₀ hp
  refine ⟨1, one_pos, ?_⟩
  rintro y c hyW ⟨z₁, hz₁, rfl⟩ ⟨a, rfl⟩ hc
  simp only [Nat.cast_one, one_mul, one_smul] at hyW hc ⊢
  obtain ⟨hxx, hww, hxw⟩ := hp
  have hyx : h.toSesq x₀ z₁ = 0 := (mem_hypComplement.1 hyW).1
  have hyw : h.toSesq w₀ z₁ = 0 := (mem_hypComplement.1 hyW).2
  have hzx : h.toSesq z₁ x₀ = 0 := by rw [sesq_swap, hyx, map_zero]
  have hzw : h.toSesq z₁ w₀ = 0 := by rw [sesq_swap, hyw, map_zero]
  have haI : (a : E) ∈ integralClosure ℤ E :=
    (mem_integralClosure_iff ℤ E).2 (RingOfIntegers.isIntegral_coe a)
  set γ := unipElem h hxx hyx hc with hγ
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists v γ La).1 hv
      rw [hγ, unipElem_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ hz₁ haI hu
    · intro hv
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      rw [hγ, unipElem_inv_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ (neg_mem hz₁)
        (conj_mem_integralClosure haI) hv
  · rw [hγ, unipElem_smul, unipMap_apply, hxx, hzx]
    simp
  · rw [hγ, unipElem_smul, unipMap_apply, hxw, hzw]
    simp only [one_mul, sub_zero, one_smul]
    abel
  · intro z hz
    rw [hγ, unipElem_smul, unipMap_apply, (mem_hypComplement.1 hz).1]
    simp only [zero_mul, zero_sub, zero_smul, add_zero, neg_smul]
    abel
end RationalUnipotent
end GroundTheory.Heights₂.Heights.FiniteCovolume
