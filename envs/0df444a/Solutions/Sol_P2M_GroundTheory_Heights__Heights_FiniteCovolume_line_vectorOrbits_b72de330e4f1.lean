-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_line_vectorOrbits_b72de330e4f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:39.021238+00:00
-- url     : https://prove2.me/submissions/83176d31-ece5-4f30-8dda-b216a24cdfb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_finset_of_finite_image_77f36989e08d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_ringMultiples_c7c1b299c311
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_unit_of_ringMultiples_eq_66cc3fabdd18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_smul_8d91b88346f9
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceUnitsFiniteIndex_proof_eec00df32b44
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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W)
    {D : ℕ} {La : AddSubgroup W} {VV : Set W} (hLa : IsDIntegral h D La) (hsub : VV ⊆ La)
    (hiso : ∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) {C : ℕ} (hC : ∀ x ∈ VV, lineIndex E La x ≤ C)
    {v₀ : W} (hv₀ : v₀ ∈ VV) :
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, x ∈ Submodule.span E {v₀} →
      ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x := by
  classical
  obtain ⟨N, hN, hγ⟩ := h₂ La v₀ hLa.isLattice hLa.integral (hsub hv₀) (hiso v₀ hv₀).1
    (hiso v₀ hv₀).2
  have hUfin : Finite ((𝓞 E)ˣ ⧸ congruenceUnits E N) := by
    have : (congruenceUnits E N).FiniteIndex := ⟨CongruenceUnitsFiniteIndex.proof E N hN⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  let L : Set W := {x ∈ VV | x ∈ Submodule.span E {v₀}}
  have hspan : ∀ x ∈ L, Submodule.span E {x} = Submodule.span E {v₀} := by
    rintro x ⟨hx, hxs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxs
    have hc : c ≠ 0 := by
      rintro rfl
      exact (hiso _ hx).1 (zero_smul E v₀)
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) v₀
  have hT : ∀ x ∈ L, ringMultiples E x ∈ {H : AddSubgroup W |
      H ≤ La ⊓ (Submodule.span E {v₀}).toAddSubgroup ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≠ 0 ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≤ C} := by
    intro x hxL
    have h1 := h₅ La x hLa.isLattice (hsub hxL.1) (hiso x hxL.1).1
    have h2 := hC x hxL.1
    unfold lineIndex at h1 h2
    rw [hspan x hxL] at h1 h2
    refine ⟨fun y hy => ?_, h1, h2⟩
    obtain ⟨a, rfl⟩ := mem_ringMultiples.1 hy
    exact ⟨hLa.isLattice.smul_mem a x (hsub hxL.1), Submodule.smul_mem _ _ hxL.2⟩
  have hTfin := h₃ (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) La hLa.isLattice.fg inf_le_left C
  choose! b hbL hb using fun H (hH : H ∈ (fun x => ringMultiples E x) '' L) => hH
  have hunit : ∀ x ∈ L, ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b (ringMultiples E x) := by
    intro x hx
    have hH : ringMultiples E x ∈ (fun x => ringMultiples E x) '' L := ⟨x, hx, rfl⟩
    exact exists_unit_of_ringMultiples_eq (hiso _ (hbL _ hH).1).1 (hb _ hH).symm
  choose! ε hε using hunit
  let f : W → AddSubgroup W × ((𝓞 E)ˣ ⧸ congruenceUnits E N) :=
    fun x => (ringMultiples E x, QuotientGroup.mk (ε x))
  have hfin : (f '' L).Finite :=
    (hTfin.prod Set.finite_univ).subset (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hT x hx, trivial⟩)
  have hP : ∀ x ∈ L, ∀ y ∈ L, f x = f y → ∃ γ ∈ latticeStab h La, γ • y = x := by
    intro x hx y hy hxy
    simp only [f, Prod.mk.injEq] at hxy
    obtain ⟨hR, hQ⟩ := hxy
    rw [QuotientGroup.eq] at hQ
    have hδ : (ε y)⁻¹ * ε x ∈ congruenceUnits E N := by
      have := inv_mem hQ
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨γ, hγS, hγv⟩ := hγ _ hδ
    refine ⟨γ, hγS, ?_⟩
    have hx' := hε x hx
    have hy' := hε y hy
    rw [hR] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy.2
    have key : (((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) * ((ε y : 𝓞 E)) = (ε x : 𝓞 E) := by
      rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
    have keyE : ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) * ((ε y : 𝓞 E) : E) = ((ε x : 𝓞 E) : E) := by
      rw [← key]
      rfl
    rw [← hc, unitary_smul_smul, hγv, smul_smul, mul_comm, ← smul_smul, hc,
      congrArg (fun t => ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) • t) hy', smul_smul, keyE, ← hx']
  obtain ⟨S, hS, hcov⟩ := exists_finset_of_finite_image L f hfin
    (fun y x => ∃ γ ∈ latticeStab h La, γ • y = x) hP
  exact ⟨S, hS.trans fun x hx => hx.1, fun x hx hxs => hcov x ⟨hx, hxs⟩⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume
