-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.unipotent_vector_group
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:53.015824+00:00
-- url     : https://prove2.me/submissions/6f3d923e-2720-4c26-a96e-d07c4271bf80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
private theorem tau_cc_eq_conj_tau (τ : E →+* ℂ) (x : E) : τ (cc x) = starRingEnd ℂ (τ x) :=
  NumberField.IsCMField.complexEmbedding_complexConj E τ x
private theorem hermC_emb_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : E →+* ℂ) (i k : Fin 2) :
    hermC τ X.Gm (Data.emb τ (u i)) (Data.emb τ (u k)) = 0 := by
  have h := congrArg τ (hiso.1 i k)
  simp only [herm, map_sum, map_mul, map_zero, tau_cc_eq_conj_tau] at h
  simp only [hermC, Data.emb]
  exact h
private theorem sum_gram_emb_mul_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : E →+* ℂ) (i k : Fin 2) :
    ∑ j, (∑ l, τ (X.Gm j l) * starRingEnd ℂ (Data.emb τ (u k) l)) * Data.emb τ (u i) j = 0 := by
  refine Eq.trans ?_ (hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ i k)
  simp only [hermC]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
private theorem zmat_eq_one_sub_smul {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ = 1 - (Complex.I * (X.c τ : ℂ)) •
      ((Matrix.of fun a i => Data.emb τ.1 (u i) a) * Matrix.of (b τ) *
        Matrix.of fun k j => ∑ l, τ.1 (X.Gm j l) * starRingEnd ℂ (Data.emb τ.1 (u k) l)) := by
  ext a j
  simp only [Data.zmat, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring
private theorem gram_conj_emb_mul_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : X.Ψ) :
    (Matrix.of fun k j => ∑ l, τ.1 (X.Gm j l) * starRingEnd ℂ (Data.emb τ.1 (u k) l)) *
      (Matrix.of fun a i => Data.emb τ.1 (u i) a) = 0 := by
  ext k i
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  exact sum_gram_emb_mul_emb_eq_zero_of_isIsoPair X u hiso τ.1 i k
private theorem one_sub_smul_mul_one_sub_smul_of_mul_eq_zero {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n (Fin 2) ℂ)
    (P : Matrix (Fin 2) n ℂ) (hPV : P * V = 0) (s : ℂ) (B B' : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - s • (V * B * P)) * (1 - s • (V * B' * P)) = 1 - s • (V * (B + B') * P) := by
  have h : V * B * P * (V * B' * P) = 0 := by
    calc V * B * P * (V * B' * P) = V * B * (P * V) * B' * P := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPV]; simp
  simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_zero,
    Matrix.mul_add, Matrix.add_mul, smul_add, sub_zero]
  abel
private theorem det_one_sub_smul_mul_of_mul_eq_zero {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n (Fin 2) ℂ)
    (P : Matrix (Fin 2) n ℂ) (hPV : P * V = 0) (s : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - s • (V * B * P)).det = 1 := by
  have e : (1 : Matrix n n ℂ) - s • (V * B * P) = 1 + (-(s • (V * B))) * P := by
    rw [Matrix.neg_mul, Matrix.smul_mul, sub_eq_add_neg]
  have h : P * (-(s • (V * B))) = 0 := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, hPV, Matrix.zero_mul, smul_zero,
      neg_zero]
  rw [e, Matrix.det_one_add_mul_comm, h, add_zero, Matrix.det_one]
private theorem zmat_mulVec_eq {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.zmat u b τ) w = fun p => w p - ∑ i, (Complex.I * (X.c τ : ℂ) *
      ∑ k, b τ i k * hermC τ.1 X.Gm w (Data.emb τ.1 (u k))) * Data.emb τ.1 (u i) p := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Data.zmat, Matrix.of_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  congr 1
  simp only [hermC, Fin.sum_univ_two, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
private theorem hermC_sub_sum_smul_expand {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (w w' : Fin r → ℂ)
    (v : Fin 2 → Fin r → ℂ) (α β : Fin 2 → ℂ) :
    hermC τ G (fun p => w p - ∑ i, α i * v i p) (fun p => w' p - ∑ i, β i * v i p) =
      hermC τ G w w' - ∑ i, starRingEnd ℂ (β i) * hermC τ G w (v i) -
        ∑ i, α i * hermC τ G (v i) w' +
          ∑ i, ∑ k, α i * starRingEnd ℂ (β k) * hermC τ G (v i) (v k) := by
  simp only [hermC, Fin.sum_univ_two, map_sub, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring
private theorem hermC_Gm_eq_starRingEnd_swap {r : ℕ} (X : Data E r) (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ X.Gm v w = starRingEnd ℂ (hermC τ X.Gm w v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← X.Gm_herm y x, tau_cc_eq_conj_tau]
  ring
private theorem hermC_zmat_mulVec_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (w w' : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.zmat u b τ) w) (Matrix.mulVec (X.zmat u b τ) w') =
      hermC τ.1 X.Gm w w' := by
  have e := hermC_sub_sum_smul_expand τ.1 X.Gm w w' (fun i => Data.emb τ.1 (u i))
    (fun i => Complex.I * (X.c τ : ℂ) * ∑ k, b τ i k * hermC τ.1 X.Gm w (Data.emb τ.1 (u k)))
    (fun i => Complex.I * (X.c τ : ℂ) * ∑ k, b τ i k * hermC τ.1 X.Gm w' (Data.emb τ.1 (u k)))
  beta_reduce at e
  rw [zmat_mulVec_eq, zmat_mulVec_eq, e]
  simp only [Fin.sum_univ_two, hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ.1, mul_zero, add_zero,
    hermC_Gm_eq_starRingEnd_swap X τ.1 (Data.emb τ.1 (u 0)) w', hermC_Gm_eq_starRingEnd_swap X τ.1 (Data.emb τ.1 (u 1)) w',
    map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
  rw [← hb τ 0 0, ← hb τ 0 1, ← hb τ 1 0, ← hb τ 1 1]
  ring
private theorem zmat_mulVec_emb_eq_self {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (i : Fin 2) :
    Matrix.mulVec (X.zmat u b τ) (Data.emb τ.1 (u i)) = Data.emb τ.1 (u i) := by
  rw [zmat_mulVec_eq]
  funext p
  simp only [hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ.1, mul_zero, Finset.sum_const_zero, zero_mul, sub_zero]
private theorem col_mul_eq_mulVec_col_natDim {r : ℕ} (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = Matrix.mulVec M (col N a) := by
  funext k
  simp only [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
private theorem gram_zmat_mul_eq_gram {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.zmat u b τ * M) = gram τ.1 X.Gm M := by
  ext a c
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col_natDim, hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ]
private theorem mat_Zb_eq_zmat_mul_mat {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl
private theorem dmin_Zb_eq_dmin {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b)
    (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
  simp only [dmin, mat_Zb_eq_zmat_mul_mat, gram_zmat_mul_eq_gram X u hiso b hb τ]
private theorem zmat_mul_zmat_eq_zmat_add {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  rw [zmat_eq_one_sub_smul X u b τ, zmat_eq_one_sub_smul X u b' τ, zmat_eq_one_sub_smul X u (b + b') τ,
    one_sub_smul_mul_one_sub_smul_of_mul_eq_zero _ _ (gram_conj_emb_mul_emb_eq_zero_of_isIsoPair X u hiso τ), Matrix.of_add_of, Pi.add_apply]
private theorem det_zmat_eq_one {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    (X.zmat u b τ).det = 1 := by
  rw [zmat_eq_one_sub_smul X u b τ]
  exact det_one_sub_smul_mul_of_mul_eq_zero _ _ (gram_conj_emb_mul_emb_eq_zero_of_isIsoPair X u hiso τ) _ _
private theorem flowMatV_uvec_eq_zmat {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    X.flowMatV (X.uvec u a τ) τ (s τ) =
      X.zmat u (fun τ' i k => s τ' * a τ' i * starRingEnd ℂ (a τ' k)) τ := by
  ext p j
  simp only [Data.flowMatV, Data.zmat, Data.uvec, Matrix.of_apply, Fin.sum_univ_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, add_mul,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : UnipotentVectorGroup (E := E) := by
  unfold UnipotentVectorGroup
  intro r X u hiso
  refine ⟨fun b b' x => ?_, fun b hb => ?_⟩
  · funext τ
    show X.zmat u b τ * (X.zmat u b' τ * mat x τ) = X.zmat u (b + b') τ * mat x τ
    rw [← Matrix.mul_assoc, zmat_mul_zmat_eq_zmat_add X u hiso]
  · have hfix := zmat_mulVec_emb_eq_self X u hiso b
    have hdom : ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := by
      intro x hx
      simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
      intro τ
      refine ⟨?_, fun i => ?_⟩
      · rw [mat_Zb_eq_zmat_mul_mat, Matrix.det_mul, det_zmat_eq_one X u hiso b, one_mul]
        exact (hx τ).1
      · rw [dmin_Zb_eq_dmin X u hiso b hb]
        exact (hx τ).2 i
    have hmaj : ∀ (x : Frame X.Ψ r) (τ : X.Ψ), x ∈ X.dom →
        X.maj (X.Zb u b x) τ (Data.emb τ.1 (u 0)) = X.maj x τ (Data.emb τ.1 (u 0)) := by
      intro x τ _
      have hv0 : ∀ w, hermC τ.1 X.Gm (Data.emb τ.1 (u 0)) (Matrix.mulVec (X.zmat u b τ) w) =
          hermC τ.1 X.Gm (Data.emb τ.1 (u 0)) w := by
        intro w
        have h := hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ (Data.emb τ.1 (u 0)) w
        rwa [hfix τ 0] at h
      simp only [Data.maj, Data.posPart, Data.gramPos, mat_Zb_eq_zmat_mul_mat, col_mul_eq_mulVec_col_natDim,
        gram_zmat_mul_eq_gram X u hiso b hb τ, hv0]
    have hD1 : ∀ x ∈ X.FramesOverBasis (u 0), X.Zb u b x ∈ X.FramesOverBasis (u 0) := by
      intro x hx
      simp only [Data.FramesOverBasis, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hdom x hx.1, fun τ => ?_⟩
      rw [hmaj x τ hx.1]
      exact hx.2 τ
    refine ⟨?_, hfix, fun τ => det_zmat_eq_one X u hiso b τ, hdom, ?_, ?_, hmaj, hD1, ?_, ?_⟩
    · intro τ w w'
      exact hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ w w'
    · intro x x' h τ
      have key : ∀ y : Frame X.Ψ r,
          Set.range (fun a : Fin X.p0 => col (mat (X.Zb u b y) τ) (Fin.castLE X.p0_le a)) =
            (Matrix.mulVecLin (X.zmat u b τ)) ''
              Set.range (fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)) := by
        intro y
        rw [← Set.range_comp]
        congr 1
      rw [key x, key x', Submodule.span_image, Submodule.span_image, h τ]
    · intro la x _
      simp only [Data.nfac, dmin_Zb_eq_dmin X u hiso b hb x]
    · intro a s x
      funext τ
      show X.zmat u b τ * (X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ) =
        X.flowMatV (X.uvec u a τ) τ (s τ) * (X.zmat u b τ * mat x τ)
      rw [flowMatV_uvec_eq_zmat X u a s τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, zmat_mul_zmat_eq_zmat_add X u hiso,
        zmat_mul_zmat_eq_zmat_add X u hiso, add_comm]
    · intro a s x
      funext τ
      exact congrArg (fun M => M * mat x τ) (flowMatV_uvec_eq_zmat X u a (fun τ => (s τ : ℂ)) τ)
end ReciprocityTheory.ChartRestriction.G.FD
