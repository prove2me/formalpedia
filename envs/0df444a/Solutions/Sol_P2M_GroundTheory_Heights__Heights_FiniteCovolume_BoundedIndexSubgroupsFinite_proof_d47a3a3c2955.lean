-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedIndexSubgroupsFinite_proof_d47a3a3c2955
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:54.676544+00:00
-- url     : https://prove2.me/submissions/54ed1cb5-4e46-4c22-b83c-876ab98ecc59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedIndexSubgroupsFinite
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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace BoundedIndexSubgroupsFinite
theorem _root_.solution (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G := by
  intro A B hB hAB C
  classical

  have : Module.Finite ℤ B :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg B).mpr hB)
  have : Module.Finite ℤ A :=
    Module.Finite.of_injective (AddSubgroup.inclusion hAB).toIntLinearMap
      (AddSubgroup.inclusion_injective hAB)

  set n := C.factorial with hn
  let K : AddSubgroup A := (nsmulAddMonoidHom n : A →+ A).range

  have : Module.Finite ℤ (A ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap
      (QuotientAddGroup.mk'_surjective K)
  have htors : Module.IsTorsion ℤ (A ⧸ K) := by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Nat.factorial_pos C).ne')⟩, ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      show (n : ℤ) • (QuotientAddGroup.mk a : A ⧸ K) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, natCast_zsmul]
      exact ⟨a, rfl⟩
  have : Finite (A ⧸ K) := Module.finite_of_fg_torsion _ htors

  have hK : ∀ H ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      K ≤ H.addSubgroupOf A := by
    rintro H ⟨-, h0, hC⟩ _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hC
    rw [AddSubgroup.mem_addSubgroupOf]
    show n • (a : G) ∈ H
    rw [hn, hk, mul_nsmul]
    exact H.nsmul_mem (H.nsmul_relIndex_mem a.2) k

  refine Set.Finite.of_finite_image (f := fun H : AddSubgroup G =>
    (QuotientAddGroup.mk '' ((H.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)))
    (Set.toFinite _) ?_
  have key : ∀ H₁ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      ∀ H₂ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      (QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)) =
        QuotientAddGroup.mk '' ((H₂.addSubgroupOf A : AddSubgroup A) : Set A) → H₁ ≤ H₂ := by
    intro H₁ h₁ H₂ h₂ he x hx
    have hxA : x ∈ A := h₁.1 hx
    have hmem : (QuotientAddGroup.mk (⟨x, hxA⟩ : A) : A ⧸ K) ∈
        QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) :=
      ⟨⟨x, hxA⟩, AddSubgroup.mem_addSubgroupOf.mpr hx, rfl⟩
    rw [he] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hd : -y + ⟨x, hxA⟩ ∈ H₂.addSubgroupOf A := hK H₂ h₂ (QuotientAddGroup.eq.mp hyx)
    have : (⟨x, hxA⟩ : A) ∈ H₂.addSubgroupOf A := by
      simpa using (H₂.addSubgroupOf A).add_mem hy hd
    exact AddSubgroup.mem_addSubgroupOf.mp this
  exact fun H₁ h₁ H₂ h₂ he => le_antisymm (key H₁ h₁ H₂ h₂ he) (key H₂ h₂ H₁ h₁ he.symm)
end BoundedIndexSubgroupsFinite
end GroundTheory.Heights₂.Heights.FiniteCovolume
