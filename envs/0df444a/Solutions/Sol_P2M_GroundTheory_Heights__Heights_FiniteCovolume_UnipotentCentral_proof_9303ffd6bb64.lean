-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_proof_9303ffd6bb64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:19.886545+00:00
-- url     : https://prove2.me/submissions/b0d1a0cc-c2f0-4070-8597-a3647fe6219f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCentral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCentral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_map_1efb3bf7d4ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_swap_62d69dcf7b6b
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_add_conj
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_smul_vecAt_b12bc12835a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipCoord_apply_32954df33c4e
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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] archMulAction
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCentral
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCentral
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (h0 : RationalUnipotent.Statement h)
    (h4 : UnipRadicalOfRational.Statement h v) (h6 : ImaginaryLatticeCocompact.Statement F E) :
    UnipotentCentral.Statement h v := by
  intro D La x₀ w₀ hD hx₀ hp K₁ hK₁
  obtain ⟨m, hm, hm'⟩ := h0 D La x₀ w₀ hD hx₀ hp
  obtain ⟨R, hR⟩ := h6 m hm
  have HP := HermAtPlace.proof h v
  have GD := GramAtData.proof h v
  have hXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← HP w, hp.1, map_zero]
  have hYY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 := fun w => by
    rw [← HP w, hp.2.1, map_zero]
  have hXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 := fun w => by
    rw [← HP w, hp.2.2, map_one]
  have hYX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1 := fun w => by
    rw [pair_swap (GD w).1, hXY, star_one]

  let f : (InfinitePlace E → ι → ℂ) → InfinitePlace E → ℂ := fun k w =>
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) + star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2
  have hf : Continuous f := by
    refine continuous_pi fun w => ?_
    have hk : Continuous fun k : InfinitePlace E → ι → ℂ => k w := continuous_apply w
    exact (continuous_const.dotProduct (continuous_const.matrix_mulVec hk)).add
      ((hk.star.dotProduct (continuous_const.matrix_mulVec hk)).div_const 2)
  obtain ⟨B, hB⟩ := hK₁.exists_bound_of_continuousOn hf.continuousOn

  let box : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) ''
    (Set.Icc (-B) B ×ˢ Set.Icc (-R) R)
  have hbox : IsCompact box := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  let T : Set (InfinitePlace E → ℂ) := Set.univ.pi fun _ => box
  have hT : IsCompact T := isCompact_univ_pi fun _ => hbox
  let Φ : (InfinitePlace E → ι → ℂ) × (InfinitePlace E → ℂ) → InfinitePlace E → ι → ℂ :=
    fun p => p.1 + fun w => p.2 w • vecAt v x₀ w
  have hΦ : Continuous Φ := continuous_fst.add (continuous_pi fun w =>
    ((continuous_apply w).comp continuous_snd).smul continuous_const)
  refine ⟨Φ '' (K₁ ×ˢ T), (hK₁.prod hT).image hΦ, ?_⟩
  rintro n ⟨t, ht⟩
  obtain ⟨k, hkK, hku⟩ : ∃ k ∈ K₁, unipCoord h v x₀ w₀ n = k + fun w => t w • vecAt v x₀ w :=
    ⟨_, ht, (sub_add_cancel _ _).symm⟩

  have hnN := mem_unipRadical.1 n.2
  have hnU := mem_archUnitary.1 (n : archUnitary h v).2
  have hu : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      vecAt v w₀ w = vecAt v w₀ w + (k w + t w • vecAt v x₀ w) := by
    intro w
    have e := congrFun hku w
    rw [unipCoord_apply, Pi.add_apply] at e
    rw [← e]
    abel
  have hXk : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) = 0 := by
    intro w
    have e := pair_map (hnU w) (vecAt v x₀ w) (vecAt v w₀ w)
    rw [(hnN w).1, hu w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hXX,
      mul_zero, add_zero] at e
    linear_combination e
  have hkX : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [pair_swap (GD w).1, hXk, star_zero]
  have hkY : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) =
      star (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w)) := fun w => pair_swap (GD w).1 _ _
  have hre : ∀ w, (t w).re = -(f k w).re := by
    intro w
    have e := pair_map (hnU w) (vecAt v w₀ w) (vecAt v w₀ w)
    rw [hu w, hYY w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXY, hXk, hkX, hkY, hYY] at e
    have e2 := congrArg Complex.re e
    simp only [mul_one, mul_zero, add_zero, zero_add, Complex.add_re, Complex.zero_re,
      Complex.star_def, Complex.conj_re] at e2
    show (t w).re = -(star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) +
      star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2).re
    rw [Complex.add_re, Complex.div_ofNat_re]
    linarith
  have hreB : ∀ w, |(t w).re| ≤ B := fun w => by
    rw [hre w, abs_neg]
    exact (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (f k) w).trans (hB k hkK))

  obtain ⟨a, ha, hRa⟩ := hR fun w => -(t w).im
  have hcre : ∀ w : InfinitePlace E, (w.embedding ((m : E) * a)).re = 0 := by
    intro w
    have e := congrArg w.embedding ha
    rw [map_add, embedding_conj (F := F) w.embedding, map_zero, Complex.add_conj] at e
    have e2 := congrArg Complex.re e
    simp only [Complex.ofReal_re, Complex.zero_re, mul_eq_zero, two_ne_zero, false_or] at e2
    exact e2
  obtain ⟨γ, hγLa, hγx, hγw, hγz⟩ := hm' 0 ((m : E) * a) (Submodule.zero_mem _)
    ⟨0, zero_mem _, (smul_zero _).symm⟩ ⟨a, rfl⟩
    (by rw [ha]; simp)
  have hsymm : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hp.2.2, map_one]
  have hγN : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀ := by
    intro z hz
    refine ⟨0, ?_⟩
    have hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀ := by
      rw [mem_hypComplement, map_sub, map_sub, map_smul, map_smul, hz, hp.1, hsymm]
      simp
    have e : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) = z - h.toSesq w₀ z • x₀ := by
      have := hγz _ hz'
      rw [map_zero, LinearMap.zero_apply, zero_smul, sub_zero] at this
      exact this
    have hγx' : (γ : W ≃ₗ[E] W) x₀ = x₀ := hγx
    have hdec : z = h.toSesq w₀ z • x₀ + (z - h.toSesq w₀ z • x₀) := by abel
    show (γ : W ≃ₗ[E] W) z = z + (0 : E) • x₀
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hγx', e, zero_smul, add_zero]
    abel
  have hδN : archEmbed h v γ ∈ unipRadical h v x₀ := h4 x₀ γ hγx hγN
  refine ⟨⟨archEmbed h v γ, hδN⟩, ⟨⟨γ, hγLa⟩, hγx, rfl⟩, ?_⟩
  have hDU := mem_archUnitary.1 (archEmbed h v γ).2
  have hD : ∀ (x : W) (w : InfinitePlace E),
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w = vecAt v (γ • x) w := fun x w => by
    rw [← archSmul_apply, archEmbed_smul_vecAt]
  have hDY : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + w.embedding ((m : E) * a) • vecAt v x₀ w := by
    intro w
    rw [hD, hγw]
    funext i
    simp [vecAt]
  have hDX : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w := fun w => by rw [hD, hγx]
  have hDk : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ k w = k w := by
    intro w
    obtain ⟨b, hb⟩ := (mem_unipRadical.1 hδN w).2 (k w) (hXk w)
    have e := pair_map (hDU w) (vecAt v w₀ w) (k w)
    rw [hb, hDY w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXk] at e
    have hb0 : b = 0 := by linear_combination e
    rw [hb, hb0, zero_smul, add_zero]
  have hcoord : unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδN⟩ * n) =
      Φ (k, fun w => t w + w.embedding ((m : E) * a)) := by
    funext w
    rw [unipCoord_apply]
    change ((((archEmbed h v γ : archUnitary h v) * (n : archUnitary h v) : archUnitary h v) :
      InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w - vecAt v w₀ w =
      k w + (t w + w.embedding ((m : E) * a)) • vecAt v x₀ w
    rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← mulVec_mulVec, hu w, mulVec_add,
      mulVec_add, mulVec_smul, hDY w, hDX w, hDk w, add_smul]
    abel
  rw [hcoord]
  refine Set.mem_image_of_mem Φ ⟨hkK, fun w _ => ?_⟩
  refine ⟨((t w + w.embedding ((m : E) * a)).re, (t w + w.embedding ((m : E) * a)).im),
    ⟨?_, ?_⟩, Complex.re_add_im (t w + w.embedding ((m : E) * a))⟩
  · rw [Complex.add_re, hcre w, add_zero]
    exact abs_le.1 (hreB w)
  · rw [Complex.add_im]
    have := abs_le.1 (hRa w)
    constructor <;> linarith [this.1, this.2]
end GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCentral
