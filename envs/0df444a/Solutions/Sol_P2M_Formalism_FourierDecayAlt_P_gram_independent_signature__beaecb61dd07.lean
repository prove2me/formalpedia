-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_gram_independent_signature__beaecb61dd07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:41.122501+00:00
-- url     : https://prove2.me/submissions/045e23ca-faac-40aa-96c4-233283dd2ff0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_Hpk_fix_of_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_herm_self_of_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_eq_zero_of_sum_normSq_nonpos
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_of_star_gramVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_mem_Uperp
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gnB_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gram_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gram_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_sig_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_star_mul_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_block_form
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.GramIndependentSignature := by
  intro k r z z' γ hstd hpos
  set V := gnB k r z z' γ with hVd
  set H := Hpk k r with hHd
  set Γ := Vᴴ * H * V with hΓd
  have hΓ : IsUnit Γ.det := gram_det z z' γ hstd hpos
  have hΓh : Γᴴ = Γ := gram_herm z z' γ
  have hHh : Hᴴ = H := GBasic.Hpk_herm k r
  have hgram : gramM k r z z' γ = Γ := gn_gramM_eq k r z z' γ
  have hform : ∀ a b, herm H (V *ᵥ a) (V *ᵥ b) = star b ⬝ᵥ (Γ *ᵥ a) := by
    intro a b; rw [herm_mulVec]

  have hli : LinearIndependent ℂ (gramVec k r z z' γ) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : V *ᵥ g = 0 := by rw [hVd, gnB_mulVec]; exact hg
    have h2 : Γ *ᵥ g = 0 := by rw [hΓd, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    have h3 : g = Γ⁻¹ *ᵥ (Γ *ᵥ g) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_mulVec]
    rw [h3, h2, Matrix.mulVec_zero]; rfl

  have hGB := gram_block_form k r z z' hstd.2.1 hstd.2.2 γ hpos.1
  have h₁ : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ, LinearMap.funLeft ℂ ℂ Sum.inr c = 0 →
      (star c ⬝ᵥ (Γ *ᵥ c)).re ≤ 0 := by
    intro c hc
    have hc' : ∀ b, c (Sum.inr b) = 0 := fun b => congrFun hc b
    rw [← hgram, hGB]
    have e : star c ⬝ᵥ (Matrix.fromBlocks (C2.Adiag k r z) (Zhat k r z z' γ) (Zhat k r z z' γ)ᴴ (C2.Adiag k r z') *ᵥ c) =
        ∑ a, star (c (Sum.inl a)) * (((if a = Fin.last r then -(Tz k r z) else 0 : ℝ) : ℂ) * c (Sum.inl a)) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hc', mul_zero, Finset.sum_const_zero, add_zero,
        Pi.star_apply, star_zero, zero_mul, C2.Adiag, Matrix.diagonal_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single a]
      · simp only [if_true]; congr 1; split_ifs <;> simp
      · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
      · simp
    rw [e, Complex.re_sum]
    apply Finset.sum_nonpos
    intro a _
    rw [star_mul_real]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
    split_ifs
    · linarith [hstd.2.1.2]
    · exact le_refl _
  have h₂ : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ, (phiL k r ∘ₗ Matrix.mulVecLin V) c = 0 →
      0 ≤ (star c ⬝ᵥ (Γ *ᵥ c)).re := by
    intro c hc
    have hfix := Hpk_fix_of_phi (V *ᵥ c) hc
    rw [← hform, herm_self_of_fix _ hfix, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  obtain ⟨Q, hQu, hQ⟩ := sig_split Γ hΓh (isUnit_iff_ne_zero.mp hΓ) (LinearMap.funLeft ℂ ℂ Sum.inr) h₁
    (phiL k r ∘ₗ Matrix.mulVecLin V) h₂
  refine ⟨hli, ⟨Q, hQu, by rw [hgram]; exact hQ⟩, ?_, ?_⟩
  ·
    intro v hv hv0
    rw [mem_Uperp] at hv
    by_contra hneg
    have hneg' : (herm H v v).re ≤ 0 := not_lt.mp hneg
    have hperp1 : ∀ d, herm H v (V *ᵥ d) = 0 := by
      intro d
      rw [herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hv, dotProduct_zero]
    have hperp2 : ∀ d, herm H (V *ᵥ d) v = 0 := by
      intro d
      rw [ggHerm_swap H hHh, hperp1, star_zero]
    set emb : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :=
      { toFun := fun c => Sum.elim 0 c
        map_add' := by intro a b; funext x; cases x <;> simp
        map_smul' := by intro a b; funext x; cases x <;> simp }
    set L : (Option (Fin (r + 1)) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
      phiL k r ∘ₗ (Matrix.mulVecLin (V * Q) ∘ₗ emb ∘ₗ LinearMap.funLeft ℂ ℂ some +
        LinearMap.smulRight (LinearMap.proj none) v)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
        Fintype.card_option, Fintype.card_fin]; omega)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set c : Fin (r + 1) → ℂ := fun j => w (some j) with hcd
    set t := w none with htd
    set ct : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := Sum.elim 0 c with hctd
    set x := (V * Q) *ᵥ ct + t • v with hxd
    have hx : L w = phiL k r x := by
      simp only [L, x, ct, c, t, emb, LinearMap.comp_apply, LinearMap.add_apply, Matrix.mulVecLin_apply,
        LinearMap.funLeft_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smulRight_apply, LinearMap.proj_apply]
      rfl
    have hLx : phiL k r x = 0 := by rw [← hx]; exact hw
    have hfix := Hpk_fix_of_phi x hLx
    have hVQ : (V * Q)ᴴ * H * (V * Q) = fromBlocks 1 0 0 (-1) := by
      rw [← hQ, Matrix.conjTranspose_mul, hΓd]; simp only [Matrix.mul_assoc]
    have haa : herm H ((V * Q) *ᵥ ct) ((V * Q) *ᵥ ct) = -∑ j, star (c j) * c j := by
      rw [herm_mulVec, hVQ]
      simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, ct, Matrix.one_apply, Matrix.neg_apply,
        Finset.sum_neg_distrib]
    have hp1 : herm H ((V * Q) *ᵥ ct) v = 0 := by rw [← Matrix.mulVec_mulVec]; exact hperp2 _
    have hp2 : herm H v ((V * Q) *ᵥ ct) = 0 := by rw [← Matrix.mulVec_mulVec]; exact hperp1 _
    have hxx : herm H x x = -∑ j, star (c j) * c j + t * conj t * herm H v v := by
      rw [hxd, herm_add_left, herm_add_right, herm_add_right, haa, herm_smul_right, hp1, herm_smul_left, hp2,
        herm_smul_left, herm_smul_right]
      ring
    have hre := congrArg Complex.re hxx
    rw [herm_self_of_fix _ hfix, Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.re_sum,
      Complex.mul_conj, Complex.re_ofReal_mul] at hre
    have hcs : ∀ j, (star (c j) * c j).re = Complex.normSq (c j) := by
      intro j; rw [mul_comm, Complex.star_def, Complex.mul_conj]; exact Complex.ofReal_re _
    simp only [hcs] at hre
    have hx0 : 0 ≤ ∑ i, Complex.normSq (x i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have ht0 : Complex.normSq t * (herm H v v).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hneg'
    have hc0 : c = 0 := eq_zero_of_sum_normSq_nonpos c (by linarith)
    have hxz : x = 0 := eq_zero_of_sum_normSq_nonpos x (by
      have : ∑ j, Complex.normSq (c j) = 0 := by rw [hc0]; simp
      linarith)
    have hct : ct = 0 := by rw [hctd, hc0]; funext y; cases y <;> rfl
    rw [hxd, hct, Matrix.mulVec_zero, zero_add] at hxz
    have ht : t = 0 := (smul_eq_zero.mp hxz).resolve_right hv0
    apply hw0
    funext o
    cases o with
    | none => exact ht
    | some j => exact congrFun hc0 j
  ·
    have hsurj : LinearMap.range (Matrix.mulVecLin (Vᴴ * H)) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      refine ⟨V *ᵥ (Γ⁻¹ *ᵥ c), ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        show Vᴴ * H * V * Γ⁻¹ = 1 from Matrix.mul_nonsing_inv _ hΓ, Matrix.one_mulVec]
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (Vᴴ * H))
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hrk
    unfold C2.Uperp
    rw [of_star_gramVec]
    show Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (Vᴴ * H))) = k - 1
    have hk := hstd.1
    omega
end Formalism.FourierDecayAlt.P
