-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:03:06.117228+00:00
-- url     : https://prove2.me/submissions/b589a19c-b955-4e16-b268-3d6214496436

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
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
open scoped Pointwise
noncomputable section
universe u
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [NoZeroSMulDivisors ℕ A]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (M : AddSubgroup A) {n : ℕ} (hn : 0 < n) :
    {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}.Finite := by
  rcases Set.eq_empty_or_nonempty {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}
    with he | ⟨L₀, hML₀, -, hL₀⟩
  · rw [he]
    exact Set.finite_empty
  have hM : M.FG := fg_of_le_fg hML₀ hL₀
  let f : A →+ A := nsmulAddMonoidHom n
  have hf : Function.Injective f := fun x y hxy => by
    have hxy' : n • x = n • y := hxy
    exact smul_right_injective A hn.ne' hxy'

  let N : AddSubgroup A := M.comap f
  have hNM : (N.map f) ≤ M := AddSubgroup.map_comap_le _ _
  have hN : N.FG := by
    have h1 : (N.map f).FG := fg_of_le_fg hNM hM
    have h2 : N.toIntSubmodule.FG := by
      refine Submodule.fg_of_fg_map_injective f.toIntLinearMap hf ?_
      have : (N.toIntSubmodule.map f.toIntLinearMap) = (N.map f).toIntSubmodule := by
        ext x
        simp
      rw [this]
      exact (Submodule.fg_iff_addSubgroup_fg _).2 h1
    exact (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have hMN : M ≤ N := fun x hx => M.nsmul_mem hx n
  let M' : AddSubgroup N := M.addSubgroupOf N
  have : AddGroup.FG N := (AddGroup.fg_iff_addSubgroup_fg N).2 hN
  have : AddGroup.FG (N ⧸ M') :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective M')
  have : Finite (N ⧸ M') := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective M' q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact x.2

  let q : AddSubgroup A → Set (N ⧸ M') := fun L =>
    QuotientAddGroup.mk' M' '' {y : N | (y : A) ∈ L}
  refine Set.Finite.of_finite_image (f := q) (Set.toFinite _) ?_
  rintro L ⟨hML, hLn, -⟩ L' ⟨hML', hL'n, -⟩ hq
  have key : ∀ L L' : AddSubgroup A, M ≤ L' → (∀ x ∈ L, n • x ∈ M) → q L ⊆ q L' → L ≤ L' := by
    intro L L' hML' hLn hsub x hx
    have hxN : x ∈ N := hLn x hx
    obtain ⟨y, hy, hyx⟩ := hsub ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hyx
    have hd : -(y : A) + x ∈ M := by
      have := AddSubgroup.mem_addSubgroupOf.1 hyx
      simpa using this
    have : x = y + (-(y : A) + x) := by abel
    rw [this]
    exact L'.add_mem hy (hML' hd)
  exact le_antisymm (key L L' hML' hLn hq.le) (key L' L hML hL'n hq.ge)
end GroundTheory.Heights₂.Heights.FiniteCovolume
