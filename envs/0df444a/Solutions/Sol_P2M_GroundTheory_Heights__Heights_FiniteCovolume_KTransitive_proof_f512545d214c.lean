-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_KTransitive_proof_f512545d214c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:00.104501+00:00
-- url     : https://prove2.me/submissions/8c631878-325f-421b-9fbe-2633aa3fad41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PKTransitive
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_isUnit_det_of_unitary
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
open GroundTheory.Automorphic Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace KTransitive
theorem _root_.solution (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : IsotropicSplit.Statement ι) (h₂ : EigenReflectionMaps.Statement ι)
    (h₃ : PhaseOnMinus.Statement ι) (_h₄ : EigenspacesOrthogonal.Statement ι) :
    KTransitive.Statement ι := by
  intro H P hmaj z z' hz hz' hzH hz'H
  obtain ⟨ha, hb, hab⟩ := h₁ H P hmaj z hzH
  obtain ⟨ha', hb', hab'⟩ := h₁ H P hmaj z' hz'H
  have hsplit : ∀ w : ι → ℂ, plusPart H P w + minusPart H P w = w := by
    intro w; ext i; simp only [plusPart, minusPart, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hPpos := hmaj.1
  have hne : ∀ w : ι → ℂ, w ≠ 0 →
      star (plusPart H P w) ⬝ᵥ (P *ᵥ plusPart H P w) =
        star (minusPart H P w) ⬝ᵥ (P *ᵥ minusPart H P w) → plusPart H P w ≠ 0 := by
    intro w hw heq h0
    apply hw
    rw [h0] at heq
    simp only [star_zero, zero_dotProduct] at heq
    have hm : minusPart H P w = 0 := by
      by_contra hm
      exact (hPpos.dotProduct_mulVec_pos hm).ne heq
    rw [← hsplit w, h0, hm, add_zero]
  set a := plusPart H P z with ha_def
  set b := minusPart H P z with hb_def
  set a' := plusPart H P z' with ha'_def
  set b' := minusPart H P z' with hb'_def
  have ha0 : a ≠ 0 := hne z hz hab
  have ha'0 : a' ≠ 0 := hne z' hz' hab'
  have hp := hPpos.dotProduct_mulVec_pos ha0
  have hq := hPpos.dotProduct_mulVec_pos ha'0
  set p := star a ⬝ᵥ (P *ᵥ a) with hp_def
  set q := star a' ⬝ᵥ (P *ᵥ a') with hq_def
  obtain ⟨hpr, hpi⟩ := Complex.lt_def.mp hp
  obtain ⟨hqr, hqi⟩ := Complex.lt_def.mp hq
  simp only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi
  set t : ℝ := Real.sqrt (p.re / q.re) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hpr hqr)
  have htt : t * t = p.re / q.re := Real.mul_self_sqrt (div_nonneg hpr.le hqr.le)
  have ht2 : (t : ℂ) * t * q = p := by
    have key : t * t * q.re = p.re := by rw [htt, div_mul_cancel₀ _ hqr.ne']
    apply Complex.ext
    · simp [Complex.mul_re, ← hqi, key]
    · simp [Complex.mul_im, ← hqi, ← hpi]
  have hscale : ∀ v : ι → ℂ, star ((t : ℂ) • v) ⬝ᵥ (P *ᵥ ((t : ℂ) • v)) =
      (t : ℂ) * t * (star v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    ring
  have hA1 : majInvolution H P *ᵥ ((t : ℂ) • a') = (1 : ℂ) • ((t : ℂ) • a') := by
    rw [mulVec_smul, ha', one_smul]
  have hAm : majInvolution H P *ᵥ ((t : ℂ) • b') = (-1 : ℂ) • ((t : ℂ) • b') := by
    rw [mulVec_smul, hb', neg_one_smul, smul_neg]
  obtain ⟨α, hα, Rp, hRpP, hRpH, hRpa, hRpfix⟩ := h₂ H P hmaj 1 (Or.inl rfl) a ((t : ℂ) • a')
    (by rw [ha, one_smul]) hA1 (by rw [hscale, ht2])
  obtain ⟨β, hβ, Rm, hRmP, hRmH, hRmb, hRmfix⟩ := h₂ H P hmaj (-1) (Or.inr rfl) b ((t : ℂ) • b')
    (by rw [hb, neg_one_smul]) hAm (by rw [hscale, ← hab', ht2, hab])
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; exact zero_ne_one hβ
  have hc : ‖α / β‖ = 1 := by rw [norm_div, hα, hβ, div_one]
  obtain ⟨hDP, hDH, hDplus, hDminus⟩ := h₃ H P hmaj (α / β) hc
  set D := phaseOnMinus H P (α / β) with hD_def
  set M := D * Rm * Rp with hM_def
  have hunit : ∀ X : Matrix ι ι ℂ, Dᴴ * X * D = X → Rmᴴ * X * Rm = X → Rpᴴ * X * Rp = X →
      Mᴴ * X * M = X := by
    intro X h1 h2 h3
    have e : Mᴴ * X * M = Rpᴴ * (Rmᴴ * (Dᴴ * X * D) * Rm) * Rp := by
      simp only [hM_def, conjTranspose_mul, Matrix.mul_assoc]
    rw [e, h1, h2, h3]
  have hMH : Mᴴ * H * M = H := hunit H hDH hRmH hRpH
  have hMP : Mᴴ * P * M = P := hunit P hDP hRmP hRpP
  have hct : ∀ X : Matrix ι ι ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i j; simp [conjTranspose_apply]
  have hRma : Rm *ᵥ a = a := hRmfix a (by rw [ha, neg_neg, one_smul])
  have hMz : M *ᵥ ((t : ℂ) • z') = α • z := by
    have hz'2 : (t : ℂ) • z' = (t : ℂ) • a' + (t : ℂ) • b' := by rw [← smul_add, hsplit z']
    rw [hz'2, hM_def, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hRpa, hRpfix _ hAm,
      mulVec_add, mulVec_smul, hRma, hRmb, mulVec_add, mulVec_smul, mulVec_smul, hDplus a ha,
      hDminus b hb, smul_smul, mul_div_cancel₀ _ hβ0, ← smul_add, hsplit z]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hdet : IsUnit M.det := isUnit_det_of_unitary (starRingEnd ℂ) hmaj.2.2.1 (by rw [hct]; exact hMH)
  refine ⟨nonsingInvUnit M hdet, ?_, ?_, (t : ℂ)⁻¹ * α, ?_⟩
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * H * M = H
    rw [hct]; exact hMH
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * P * M = P
    rw [hct]; exact hMP
  · show M *ᵥ z' = ((t : ℂ)⁻¹ * α) • z
    rw [mulVec_smul] at hMz
    rw [mul_smul, ← hMz, smul_smul, inv_mul_cancel₀ htc, one_smul]
end KTransitive
end GroundTheory.Heights₂.Heights.FiniteCovolume
