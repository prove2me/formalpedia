-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdelicCovolumeFinite_proof_ee0a0cdb2fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:53.300061+00:00
-- url     : https://prove2.me/submissions/d5af7dbd-9e28-42f7-8210-853e949b5a16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicLattices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdelicCovolumeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_injective_6d08bfcd17b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_countable_unitaryGroup_379daacf6d24
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_refl
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77
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
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace AdelicCovolumeFinite
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    [FiniteDimensional E W] (h₁ : LatticeOrbitsFinite.Statement h)
    (h₂ : ArithmeticCovolumeFinite.Statement h v) (h₃ : ArchimedeanUnitaryEquiv.Statement h v)
    (h₄ : AdelicLatticeDictionary.Statement h v)
    (h₅ : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v := by
  classical
  intro μ _
  obtain ⟨ψ, hψ⟩ := h₃
  obtain ⟨K, D, L, hKc, hKo, hLD, hLeq, hLinj⟩ := h₄
  let e : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
      unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
      archUnitary h v × unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
    { toMulEquiv := MulEquiv.prodCongr ψ.toMulEquiv (MulEquiv.refl _)
      continuous_toFun := (ψ.continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun := (ψ.symm.continuous.comp continuous_fst).prodMk continuous_snd }
  let Φ := (adeleSplit h v).trans e
  have hΦ₁ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).1 = archEmbed h v γ :=
    fun γ => hψ γ
  have hΦ₂ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).2 =
      (adeleSplit h v (hermitianDiagonal h v γ)).2 := fun γ => rfl
  haveI := countable_unitaryGroup h v
  haveI : Countable (hermitianDiagonal h v).range := by
    refine Function.Surjective.countable (f := fun γ : h.unitaryGroup =>
      (⟨hermitianDiagonal h v γ, γ, rfl⟩ : (hermitianDiagonal h v).range)) ?_
    rintro ⟨_, γ, rfl⟩
    exact ⟨γ, rfl⟩

  obtain ⟨S₀, hS₀, hS₀cov⟩ := h₁ D
  let r : AddSubgroup W → unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) := fun L₀ => if hL : ∃ y, L y = L₀ then hL.choose else 1
  have hr : ∀ y, L (r (L y)) = L y := fun y => by
    have hL : ∃ y', L y' = L y := ⟨y, rfl⟩
    simp only [r, dif_pos hL]
    exact hL.choose_spec

  have hstab : ∀ (γ : h.unitaryGroup) (s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F)),
      γ ∈ latticeStab h (L s) ↔ s⁻¹ * (Φ (hermitianDiagonal h v γ)).2 * s ∈ K := by
    intro γ s
    rw [latticeStab, MulAction.mem_stabilizer_iff, hΦ₂, ← hLeq, eq_comm, hLinj, mul_assoc]
  have hslice : ∀ s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F), sliceGroup Φ (hermitianDiagonal h v).range K s =
      archLatticeGroup h v (L s) := by
    intro s
    ext x
    rw [mem_sliceGroup, archLatticeGroup, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨γ, rfl⟩, hk, rfl⟩
      exact ⟨γ, (hstab γ s).2 hk, (hΦ₁ γ).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hermitianDiagonal h v γ, ⟨γ, rfl⟩, (hstab γ s).1 hγ, hΦ₁ γ⟩
  obtain ⟨FD, hFD, hfin⟩ := h₅ Φ (hermitianDiagonal h v).range K (hS₀.toFinset.image r) hKc hKo
    (by
      rintro _ ⟨γ, rfl⟩ h1
      rw [hΦ₁, ← (archEmbed h v).map_one] at h1
      rw [archEmbed_injective h v h1, map_one])
    (by
      intro y
      obtain ⟨L₀, hL₀, g, hg⟩ := hS₀cov (L y) (hLD y)
      have hL₀' : L₀ = L ((adeleSplit h v (hermitianDiagonal h v g⁻¹)).2 * y) := by
        rw [hLeq, ← hg, smul_smul, inv_mul_cancel, one_smul]
      have hs : L (r L₀) = L₀ := by rw [hL₀']; exact hr _
      have hk : ((Φ (hermitianDiagonal h v g)).2 * r L₀)⁻¹ * y ∈ K := by
        rw [← hLinj, hΦ₂, hLeq, hs, hg]
      refine ⟨hermitianDiagonal h v g, ⟨g, rfl⟩, r L₀, ?_, _, hk, ?_⟩
      · exact Finset.mem_image_of_mem r (hS₀.mem_toFinset.2 hL₀)
      · group)
    (by
      intro s _ μ₁ _
      rw [hslice s]
      exact h₂ μ₁ D (L s) (hLD s))
    μ
  exact ⟨FD, hFD, hfin⟩
end AdelicCovolumeFinite
end GroundTheory.Heights₂.Heights.FiniteCovolume
