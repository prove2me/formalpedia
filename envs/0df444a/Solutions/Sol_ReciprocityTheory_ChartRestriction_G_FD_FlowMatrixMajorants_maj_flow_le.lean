-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.maj_flow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:04:55.244315+00:00
-- url     : https://prove2.me/submissions/4890a76b-348a-4a70-a7c7-be464715f353

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_Hf_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_maj_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_herm_eq_Hf_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC σ G (∑ k, u k • v k) y = ∑ k, u k * hermC σ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC σ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h
private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC σ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC σ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC σ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h
private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma hermC_smul_sub_right_lemma_4 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) = (X.gramPos x τ)⁻¹ by
      rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
private lemma maj_eq_lemma_7 (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    X.maj x τ v = (hermC τ.1 X.Gm (X.jp x τ v) v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.jp
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp
private lemma flowMat_mulVec_lemma_10 (t : ℝ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext i
  show ∑ b, X.flowMat ξ τ t i b * w b = _
  simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, hermC, Data.emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
end FlowMatrixMajorants
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (t : ℝ) (u : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) ≤
      (1 + X.c τ * |t| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ u := by
  have hHs : ∀ p q, conj (X.Hf x τ p q) = X.Hf x τ q p := by
    intro p q
    unfold Data.Hf
    rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_4, hermC_smul_sub_left_lemma_3,
      hermC_ppos_lemma_5 X τ x q p, map_ofNat]
  have hN : ∀ v, X.maj x τ v = (X.Hf x τ v v).re := fun v => maj_eq_lemma_7 X τ x v
  have hreal : ∀ v, X.Hf x τ v v = ((X.maj x τ v : ℝ) : ℂ) := by
    intro v
    rw [hN]
    exact (Complex.conj_eq_iff_re.mp (hHs v v)).symm
  have hnn : ∀ v, 0 ≤ X.maj x τ v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [hN]
      simp [Data.Hf, hermC]
    · exact (X.maj_pos hx τ hv).le
  have hsl : ∀ (a : ℂ) p q, X.Hf x τ (a • p) q = a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    rw [X.ppos_smul_eq x τ]
    simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsr : ∀ (a : ℂ) p q, X.Hf x τ p (a • q) = conj a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hexp : ∀ (α β : ℂ) p q, X.Hf x τ (α • p + β • q) (α • p + β • q) =
      α * conj α * X.Hf x τ p p + α * conj β * X.Hf x τ p q + β * conj α * X.Hf x τ q p +
        β * conj β * X.Hf x τ q q := by
    intro α β p q
    simp only [Hf_add_left X τ, Hf_add_right X τ, hsl, hsr]
    ring
  have hCS : ∀ p q, Complex.normSq (X.Hf x τ p q) ≤ X.maj x τ p * X.maj x τ q := by
    intro p q
    by_cases hq : q = 0
    · subst hq
      have h0 : X.Hf x τ p 0 = 0 := by simp [Data.Hf, hermC]
      rw [h0, map_zero]
      exact mul_nonneg (hnn p) (hnn 0)
    · have hn := X.maj_pos hx τ hq
      obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ p q := ⟨_, rfl⟩
      have h0 := hnn (((X.maj x τ q : ℝ) : ℂ) • p + (-z) • q)
      rw [hN, hexp, hreal p, hreal q, ← hHs p q, ← hz] at h0
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im,
        map_neg] at h0
      rw [← hz, Complex.normSq_apply]
      nlinarith [h0, hn]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = hermC τ.1 X.Gm u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = I * (X.c τ : ℂ) * (t : ℂ) * ℓ := ⟨_, rfl⟩
  have hMu : Matrix.mulVec (X.flowMat ξ τ t) u = (1 : ℂ) • u + (-β) • Data.emb τ.1 ξ := by
    rw [flowMat_mulVec_lemma_10 X ξ τ t u, ← hℓ, ← hβ, one_smul, neg_smul, sub_eq_add_neg]
  obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  have hval : X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) = X.maj x τ u -
      2 * (conj β * z).re + Complex.normSq β * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hN, hMu, hexp, hreal u, hreal (Data.emb τ.1 ξ), ← hHs u (Data.emb τ.1 ξ), ← hz]
    have e1 : β * conj z = conj (conj β * z) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    have e2 : β * conj β = (Complex.normSq β : ℂ) := Complex.mul_conj β
    simp only [map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg]
    rw [e1, e2]
    simp only [Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hnβ : ‖β‖ = X.c τ * |t| * ‖ℓ‖ := by
    rw [hβ, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, one_mul]
  have hL : ‖ℓ‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hℓ, herm_eq_Hf_jp X τ hx, ← Complex.normSq_eq_norm_sq, ← maj_jp X τ hx (Data.emb τ.1 ξ)]
    exact hCS _ _
  have hZ : ‖z‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hz, ← Complex.normSq_eq_norm_sq]
    exact hCS _ _
  have hre : -(2 * (conj β * z).re) ≤ 2 * ‖β‖ * ‖z‖ := by
    have h1 := Complex.abs_re_le_norm (conj β * z)
    rw [norm_mul, Complex.norm_conj] at h1
    linarith [neg_abs_le (conj β * z).re]
  have hLZ : ‖ℓ‖ * ‖z‖ ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    nlinarith [sq_nonneg (‖ℓ‖ - ‖z‖), norm_nonneg ℓ, norm_nonneg z]
  have hk : 0 ≤ X.c τ * |t| := mul_nonneg hc0 (abs_nonneg t)
  have hb : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := hnn _
  have h1 := mul_le_mul_of_nonneg_left hLZ hk
  have h2 := mul_le_mul_of_nonneg_left hL (mul_nonneg (sq_nonneg (X.c τ * |t|)) hb)
  rw [hval, Complex.normSq_eq_norm_sq, hnβ]
  rw [hnβ] at hre
  nlinarith [h1, h2, hre]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
