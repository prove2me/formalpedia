-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.relative_entropy_variational
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:08:28.507295+00:00
-- url     : https://prove2.me/submissions/f25f1e80-10a4-4a38-a548-033abfbeb472

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- overlap matrix of the two eigenbases -/
noncomputable def ov {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) : Matrix I I ℂ :=
  star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hN.eigenvectorUnitary : Matrix I I ℂ)

noncomputable def w {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) : ℝ :=
  ‖ov hR hN i j‖ ^ 2

lemma ov_unitary {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) :
    ov hR hN * star (ov hR hN) = 1 := by
  unfold ov
  have hU : star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hR.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hV : (hN.eigenvectorUnitary : Matrix I I ℂ) * star (hN.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (hN.eigenvectorUnitary : Matrix I I ℂ),
    hV, Matrix.one_mul, hU]

lemma w_row {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i : I) :
    ∑ j, w hR hN i j = 1 := by
  have h := congrFun (congrFun (ov_unitary hR hN) i) i
  rw [mul_apply, one_apply_eq] at h
  have : (∑ j, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj']
  exact_mod_cast this

lemma w_nonneg {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    0 ≤ w hR hN i j := by unfold w; positivity

lemma tr_cfc_cfc {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f R * cfc g N).trace =
      ∑ i, ∑ j, ((f (hR.eigenvalues i) * g (hN.eigenvalues j) * w hR hN i j : ℝ) : ℂ) := by
  rw [hR.cfc_eq, hN.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  set Df := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR.eigenvalues)
  set Dg := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hN.eigenvalues)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hR.eigenvectorUnitary).2
  have : (U * Df * star U * (V * Dg * star V)).trace = (Df * (star U * V) * Dg * star (star U * V)).trace := by
    rw [star_mul, star_star]
    rw [show U * Df * star U * (V * Dg * star V) = U * (Df * (star U * V) * Dg * (star V * U)) * star U by
      simp only [Matrix.mul_assoc]; rw [hU']; simp]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [this]
  change (Df * ov hR hN * Dg * star (ov hR hN)).trace = _
  have hE : ∀ i k, (Df * ov hR hN * Dg) i k =
      ((f (hR.eigenvalues i) : ℝ) : ℂ) * ov hR hN i k * ((g (hN.eigenvalues k) : ℝ) : ℂ) := by
    intro i k; simp [Df, Dg, diagonal_mul, mul_diagonal]
  simp only [Matrix.trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, star_apply]
  simp only [w, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.mul_conj', RCLike.star_def]
  ring

lemma ov_apply {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    ov hR hN i j = star (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hN.eigenvectorBasis j).ofLp := by
  simp only [ov, mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, dotProduct, Pi.star_apply]

lemma supp_fwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin) (i j : I)
    (hi : hR.eigenvalues i ≠ 0) (hj : hN.eigenvalues j = 0) : ov hR hN i j = 0 := by
  set b := (hR.eigenvectorBasis i).ofLp
  set v := (hN.eigenvectorBasis j).ofLp
  have hNv : N *ᵥ v = 0 := by rw [hN.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hRv : R *ᵥ v = 0 := by
    have := h (show v ∈ LinearMap.ker N.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have key : ((hR.eigenvalues i : ℝ) : ℂ) * (star b ⬝ᵥ v) = 0 := by
    have hb : R *ᵥ b = hR.eigenvalues i • b := hR.mulVec_eigenvectorBasis i
    have : star (R *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (R *ᵥ v) := by
      rw [star_mulVec, hR.eq, dotProduct_mulVec]
    rw [hRv, dotProduct_zero, hb, star_smul] at this
    rw [← this, smul_dotProduct]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [ov_apply]
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (by exact_mod_cast h1) hi
  · exact h1

lemma spec_mulVec {R : Matrix I I ℂ} (hR : R.IsHermitian) (x : I → ℂ) :
    R *ᵥ x = (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ
      (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x)) := by
  conv_lhs => rw [hR.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]

lemma supp_bwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ i j, hR.eigenvalues i ≠ 0 → hN.eigenvalues j = 0 → ov hR hN i j = 0) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  have hV' : star V * V = 1 := Unitary.star_mul_self_of_mem (hN.eigenvectorUnitary).2
  set c := star V *ᵥ x
  have hc : ∀ j, hN.eigenvalues j ≠ 0 → c j = 0 := by
    intro j hj
    have h1 : star V *ᵥ (N *ᵥ x) = 0 := by rw [hx, mulVec_zero]
    rw [spec_mulVec hN, mulVec_mulVec, hV', one_mulVec] at h1
    have := congrFun h1 j
    rw [mulVec_diagonal] at this
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd (by simpa using h2) hj
    · exact h2
  have hUx : star U *ᵥ x = ov hR hN *ᵥ c := by
    rw [show ov hR hN = star U * V from rfl, mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hD : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star U *ᵥ x) = 0 := by
    ext i
    rw [hUx, mulVec_diagonal, Pi.zero_apply]
    by_cases hi : hR.eigenvalues i = 0
    · simp [hi]
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      by_cases hj : hN.eigenvalues j = 0
      · rw [h i j hi hj, zero_mul]
      · rw [hc j hj, mul_zero]
  rw [spec_mulVec hR, hD, mulVec_zero]

end X5OL
end X5mod_OL_Base

section X5mod_PQ_Key
open Matrix
open scoped ComplexOrder

namespace X5PQ

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma scal (z Y : ℂ) {c : ℝ} (hc : 0 < c) : 2 * (star z * Y).re - c * ‖Y‖ ^ 2 ≤ ‖z‖ ^ 2 / c := by
  rw [le_div_iff₀ hc]
  have h1 : ‖Y‖ ^ 2 = Y.re ^ 2 + Y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h3 : (star z * Y).re = z.re * Y.re + z.im * Y.im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (z.re - c * Y.re), sq_nonneg (z.im - c * Y.im)]

lemma scal' (z Y : ℂ) {c : ℝ} (hc : 0 ≤ c) (hz : c = 0 → z = 0) :
    2 * (star z * Y).re - c * ‖Y‖ ^ 2 ≤ ‖z‖ ^ 2 / c := by
  rcases hc.lt_or_eq with hc | hc
  · exact scal z Y hc
  · subst hc; simp [hz rfl]

lemma diag_sandwich (p : Matrix I I ℂ) (y : I → ℝ) (a : I) :
    (pᴴ * diagonal (fun i => (y i : ℂ)) * p) a a = ((∑ i, y i * ‖p i a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, conjTranspose_apply, ← Complex.conj_mul', RCLike.star_def]
  ring

lemma row_sum (M : Matrix I I ℂ) (a : I) :
    (M * Mᴴ) a a = ((∑ b, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]; push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [conjTranspose_apply, ← Complex.mul_conj', RCLike.star_def]

lemma col_sum (M : Matrix I I ℂ) (b : I) :
    (Mᴴ * M) b b = ((∑ a, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]; push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conjTranspose_apply, ← Complex.conj_mul', RCLike.star_def]

theorem key (p q : Matrix I I ℂ) (hp : p * pᴴ = 1) (hq : q * qᴴ = 1)
    (lam mu : I → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : ∀ a, 0 ≤ lam a) (hm : ∀ b, 0 ≤ mu b)
    (hsupp : ∀ a b, A * lam a + B * mu b = 0 → (lam a : ℂ) * (pᴴ * q) a b = 0) :
    ∑ i, (∑ a, lam a * ‖p i a‖ ^ 2) ^ 2 /
        (A * (∑ a, lam a * ‖p i a‖ ^ 2) + B * (∑ b, mu b * ‖q i b‖ ^ 2)) ≤
      ∑ a, ∑ b, ‖(pᴴ * q) a b‖ ^ 2 * lam a ^ 2 / (A * lam a + B * mu b) := by
  set r := fun i => ∑ a, lam a * ‖p i a‖ ^ 2 with hr
  set s := fun i => ∑ b, mu b * ‖q i b‖ ^ 2 with hs
  set o := pᴴ * q
  set y : I → ℝ := fun i => r i / (A * r i + B * s i)
  set D := diagonal (fun i => (y i : ℂ))
  set Y := pᴴ * D * q
  have hr0 : ∀ i, 0 ≤ r i := fun i => Finset.sum_nonneg fun a _ => mul_nonneg (hl a) (by positivity)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Finset.sum_nonneg fun a _ => mul_nonneg (hm a) (by positivity)
  -- per-i identity
  have hi : ∀ i, r i ^ 2 / (A * r i + B * s i) = 2 * y i * r i - y i ^ 2 * (A * r i + B * s i) := by
    intro i
    by_cases h0 : A * r i + B * s i = 0
    · simp [y, h0]
    · simp only [y]; field_simp; ring
  have hDD : D * D = diagonal (fun i => ((y i ^ 2 : ℝ) : ℂ)) := by
    simp only [D, diagonal_mul_diagonal]; congr 1; ext i; push_cast; ring
  -- three identities
  have h1 : ∀ a, (∑ b, star (o a b) * Y a b).re = ∑ i, y i * ‖p i a‖ ^ 2 := by
    intro a
    have e : Y * oᴴ = pᴴ * D * p := by
      simp only [Y, o, conjTranspose_mul, conjTranspose_conjTranspose]
      rw [show pᴴ * D * q * (qᴴ * p) = pᴴ * D * (q * qᴴ) * p by simp only [Matrix.mul_assoc], hq,
        Matrix.mul_one]
    have := congrFun (congrFun e a) a
    rw [diag_sandwich, Matrix.mul_apply] at this
    rw [show (∑ b, star (o a b) * Y a b) = ∑ b, Y a b * oᴴ b a by
      refine Finset.sum_congr rfl fun b _ => ?_; rw [conjTranspose_apply, mul_comm], this,
      Complex.ofReal_re]
  have h2 : ∀ a, ∑ b, ‖Y a b‖ ^ 2 = ∑ i, y i ^ 2 * ‖p i a‖ ^ 2 := by
    intro a
    have e : Y * Yᴴ = pᴴ * diagonal (fun i => ((y i ^ 2 : ℝ) : ℂ)) * p := by
      simp only [Y, conjTranspose_mul, conjTranspose_conjTranspose]
      have hD : Dᴴ = D := by simp [D, diagonal_conjTranspose]
      rw [hD, show pᴴ * D * q * (qᴴ * (D * p)) = pᴴ * D * (q * qᴴ) * D * p by simp only [Matrix.mul_assoc],
        hq, Matrix.mul_one, Matrix.mul_assoc (pᴴ) D D, hDD]
    have := congrFun (congrFun e a) a
    rw [row_sum, diag_sandwich] at this
    exact_mod_cast this
  have h3 : ∀ b, ∑ a, ‖Y a b‖ ^ 2 = ∑ i, y i ^ 2 * ‖q i b‖ ^ 2 := by
    intro b
    have e : Yᴴ * Y = qᴴ * diagonal (fun i => ((y i ^ 2 : ℝ) : ℂ)) * q := by
      simp only [Y, conjTranspose_mul, conjTranspose_conjTranspose]
      have hD : Dᴴ = D := by simp [D, diagonal_conjTranspose]
      rw [hD, show qᴴ * (D * p) * (pᴴ * D * q) = qᴴ * D * (p * pᴴ) * D * q by simp only [Matrix.mul_assoc],
        hp, Matrix.mul_one, Matrix.mul_assoc (qᴴ) D D, hDD]
    have := congrFun (congrFun e b) b
    rw [col_sum, diag_sandwich] at this
    exact_mod_cast this
  -- termwise bound
  have hterm : ∀ a b, 2 * lam a * (star (o a b) * Y a b).re - (A * lam a + B * mu b) * ‖Y a b‖ ^ 2 ≤
      ‖o a b‖ ^ 2 * lam a ^ 2 / (A * lam a + B * mu b) := by
    intro a b
    have := scal' ((lam a : ℂ) * o a b) (Y a b) (c := A * lam a + B * mu b)
      (add_nonneg (mul_nonneg hA (hl a)) (mul_nonneg hB (hm b))) (hsupp a b)
    have e1 : (star ((lam a : ℂ) * o a b) * Y a b).re = lam a * (star (o a b) * Y a b).re := by
      rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    have e2 : ‖(lam a : ℂ) * o a b‖ ^ 2 = ‖o a b‖ ^ 2 * lam a ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hl a)]; ring
    rw [e1, e2] at this; linarith
  calc ∑ i, r i ^ 2 / (A * r i + B * s i)
      = ∑ i, (2 * y i * r i - y i ^ 2 * (A * r i + B * s i)) := Finset.sum_congr rfl fun i _ => hi i
    _ = ∑ a, ∑ b, (2 * lam a * (star (o a b) * Y a b).re - (A * lam a + B * mu b) * ‖Y a b‖ ^ 2) := by
      have L : ∑ a, ∑ b, (2 * lam a * (star (o a b) * Y a b).re - (A * lam a + B * mu b) * ‖Y a b‖ ^ 2)
          = 2 * ∑ a, lam a * (∑ b, star (o a b) * Y a b).re - A * ∑ a, lam a * ∑ b, ‖Y a b‖ ^ 2
            - B * ∑ b, mu b * ∑ a, ‖Y a b‖ ^ 2 := by
        simp only [Complex.re_sum, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun b a => B * (mu b * ‖Y a b‖ ^ 2))]
        simp only [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [L]
      simp only [h1, h2, h3, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun a i => 2 * (lam a * (y i * ‖p i a‖ ^ 2))),
        Finset.sum_comm (f := fun a i => A * (lam a * (y i ^ 2 * ‖p i a‖ ^ 2))),
        Finset.sum_comm (f := fun b i => B * (mu b * (y i ^ 2 * ‖q i b‖ ^ 2))),
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [r, s, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b

end X5PQ
end X5mod_PQ_Key

section X5mod_DP_Var
open Matrix
open scoped ComplexOrder

namespace X5DP

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def G (A B : ℝ) {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) : ℝ :=
  ∑ a, ∑ b, X5OL.w hX hY a b * hX.eigenvalues a ^ 2 / (A * hX.eigenvalues a + B * hY.eigenvalues b)

noncomputable def val (A B : ℝ) (X Y Z : Matrix I I ℂ) : ℝ :=
  2 * (Zᴴ * X).trace.re - A * (Zᴴ * X * Z).trace.re - B * (Z * Y * Zᴴ).trace.re

lemma spec_eq {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix I I ℂ) * diagonal (fun a => ((hX.eigenvalues a : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  conv_lhs => rw [hX.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]; rfl

lemma tr_spec (M : Matrix I I ℂ) {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (M * X).trace = ∑ a, ((hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * M *
      (hX.eigenvectorUnitary : Matrix I I ℂ)) a a * ((hX.eigenvalues a : ℝ) : ℂ) := by
  set E := (hX.eigenvectorUnitary : Matrix I I ℂ)
  conv_lhs => rw [spec_eq hX]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp only [Matrix.trace, diag_apply, mul_diagonal]
  rfl

lemma EE {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix I I ℂ) * (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2

lemma EE' {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix I I ℂ) = 1 := by
  rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2

/-- `val` in the joint eigen-coordinates `Z' = Eᴴ Z F`. -/
lemma val_coord (A B : ℝ) {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (Z : Matrix I I ℂ) :
    val A B X Y Z = ∑ a, ∑ b, (2 * hX.eigenvalues a *
      (star (X5OL.ov hX hY a b) * ((hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * Z *
        (hY.eigenvectorUnitary : Matrix I I ℂ)) a b).re -
      (A * hX.eigenvalues a + B * hY.eigenvalues b) *
        ‖((hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * Z * (hY.eigenvectorUnitary : Matrix I I ℂ)) a b‖ ^ 2) := by
  set E := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set F := (hY.eigenvectorUnitary : Matrix I I ℂ)
  set Z' := Eᴴ * Z * F
  set o := X5OL.ov hX hY
  have ho : o = Eᴴ * F := by simp [o, X5OL.ov, E, F, star_eq_conjTranspose]
  -- three identities
  have i1 : Eᴴ * Zᴴ * E = (Z' * oᴴ)ᴴ := by
    rw [ho]; simp only [Z', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F, EE hY, Matrix.one_mul]
  have i2 : Eᴴ * (Z * Zᴴ) * E = Z' * Z'ᴴ := by
    simp only [Z', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F, EE hY, Matrix.one_mul]
  have i3 : Fᴴ * (Zᴴ * Z) * F = Z'ᴴ * Z' := by
    simp only [Z', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E (Eᴴ), EE hX, Matrix.one_mul]
  have t1 : (Zᴴ * X).trace.re = ∑ a, ∑ b, hX.eigenvalues a * (star (o a b) * Z' a b).re := by
    rw [tr_spec _ hX, i1, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conjTranspose_apply, mul_comm, Complex.re_ofReal_mul, Complex.star_def, Complex.conj_re,
      Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [conjTranspose_apply, mul_comm (Z' a b)]; rfl
  have t2 : (Zᴴ * X * Z).trace.re = ∑ a, ∑ b, hX.eigenvalues a * ‖Z' a b‖ ^ 2 := by
    rw [Matrix.trace_mul_cycle, tr_spec _ hX, i2, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X5PQ.row_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have t3 : (Z * Y * Zᴴ).trace.re = ∑ a, ∑ b, hY.eigenvalues b * ‖Z' a b‖ ^ 2 := by
    rw [Matrix.trace_mul_cycle, tr_spec _ hY, i3, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [X5PQ.col_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold val
  rw [t1, t2, t3]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma var_le (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) {X Y : Matrix I I ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef)
    (hs : ∀ a b, A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b = 0 →
      (hX.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX.isHermitian hY.isHermitian a b = 0)
    (Z : Matrix I I ℂ) : val A B X Y Z ≤ G A B hX.isHermitian hY.isHermitian := by
  rw [val_coord A B hX.isHermitian hY.isHermitian]
  unfold G
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  set l := hX.isHermitian.eigenvalues a
  set m := hY.isHermitian.eigenvalues b
  set o := X5OL.ov hX.isHermitian hY.isHermitian a b
  set y := ((hX.isHermitian.eigenvectorUnitary : Matrix I I ℂ)ᴴ * Z *
    (hY.isHermitian.eigenvectorUnitary : Matrix I I ℂ)) a b
  have hl : 0 ≤ l := hX.eigenvalues_nonneg a
  have hm : 0 ≤ m := hY.eigenvalues_nonneg b
  have := X5PQ.scal' ((l : ℂ) * o) y (c := A * l + B * m)
    (add_nonneg (mul_nonneg hA hl) (mul_nonneg hB hm)) (hs a b)
  have e1 : (star ((l : ℂ) * o) * y).re = l * (star o * y).re := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  have e2 : ‖(l : ℂ) * o‖ ^ 2 = X5OL.w hX.isHermitian hY.isHermitian a b * l ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl, X5OL.w]; ring
  rw [e1, e2] at this; linarith

lemma var_eq (A B : ℝ) {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∃ Z, val A B X Y Z = G A B hX hY := by
  set E := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set F := (hY.eigenvectorUnitary : Matrix I I ℂ)
  set o := X5OL.ov hX hY
  set Z' : Matrix I I ℂ := Matrix.of fun a b => ((hX.eigenvalues a : ℝ) : ℂ) * o a b /
    ((A * hX.eigenvalues a + B * hY.eigenvalues b : ℝ) : ℂ)
  refine ⟨E * Z' * Fᴴ, ?_⟩
  rw [val_coord A B hX hY]
  have hZ : Eᴴ * (E * Z' * Fᴴ) * F = Z' := by
    simp only [Matrix.mul_assoc]; rw [EE' hY, Matrix.mul_one, ← Matrix.mul_assoc, EE' hX, Matrix.one_mul]
  rw [hZ]
  unfold G
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  set l := hX.eigenvalues a
  set c := A * hX.eigenvalues a + B * hY.eigenvalues b
  have hw : X5OL.w hX hY a b = ‖o a b‖ ^ 2 := rfl
  simp only [Z', Matrix.of_apply]
  rw [hw]
  by_cases hc : c = 0
  · simp [c, hc] at *
  · have e1 : (star (o a b) * ((l : ℂ) * o a b / (c : ℂ))).re = l * ‖o a b‖ ^ 2 / c := by
      rw [show star (o a b) * ((l : ℂ) * o a b / (c : ℂ)) = (((l / c * ‖o a b‖ ^ 2 : ℝ)) : ℂ) by
        have h0 : star (o a b) * o a b = ((‖o a b‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.star_def, Complex.conj_mul']; push_cast; rfl
        calc star (o a b) * ((l : ℂ) * o a b / (c : ℂ)) = (l : ℂ) / c * (star (o a b) * o a b) := by ring
          _ = _ := by rw [h0]; push_cast; ring]
      rw [Complex.ofReal_re]; ring
    have e2 : ‖(l : ℂ) * o a b / (c : ℂ)‖ ^ 2 = l ^ 2 * ‖o a b‖ ^ 2 / c ^ 2 := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, div_pow, mul_pow, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs]
    rw [e1, e2]
    field_simp
    ring

end X5DP
end X5mod_DP_Var

section X5mod_DP_KS
open Matrix
open scoped ComplexOrder

namespace X5DP

variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype J]

def Φ (K : J → Matrix κ ι ℂ) (X : Matrix ι ι ℂ) : Matrix κ κ ℂ := ∑ j, K j * X * (K j)ᴴ
def Φd (K : J → Matrix κ ι ℂ) (Q : Matrix κ κ ℂ) : Matrix ι ι ℂ := ∑ j, (K j)ᴴ * Q * K j

lemma tr_nonneg' {r s : Type*} [Fintype r] [Fintype s] (M : Matrix r s ℂ) : 0 ≤ (Mᴴ * M).trace.re := by
  simp only [Matrix.trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']
  norm_cast
  positivity

lemma cs {r : Type*} [Fintype r] (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    (M : J → Matrix κ r ℂ) :
    ((∑ j, (K j)ᴴ * M j)ᴴ * (∑ j, (K j)ᴴ * M j)).trace.re ≤ ∑ j, ((M j)ᴴ * M j).trace.re := by
  set V := ∑ j, (K j)ᴴ * M j
  have hV : ∑ j, (M j)ᴴ * K j = Vᴴ := by
    simp only [V, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose]
  have h0 : 0 ≤ ∑ j, ((M j - K j * V)ᴴ * (M j - K j * V)).trace.re :=
    Finset.sum_nonneg fun j _ => tr_nonneg' _
  have hexp : ∑ j, (M j - K j * V)ᴴ * (M j - K j * V) =
      ∑ j, (M j)ᴴ * M j - Vᴴ * V := by
    have e : ∀ j, (M j - K j * V)ᴴ * (M j - K j * V) =
        (M j)ᴴ * M j - ((M j)ᴴ * K j) * V - Vᴴ * ((K j)ᴴ * M j) + Vᴴ * ((K j)ᴴ * K j) * V := by
      intro j
      simp only [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    have s1 : ∑ j, ((M j)ᴴ * K j) * V = Vᴴ * V := by rw [← Matrix.sum_mul, hV]
    have s2 : ∑ j, Vᴴ * ((K j)ᴴ * M j) = Vᴴ * V := by rw [← Matrix.mul_sum]
    have s3 : ∑ j, Vᴴ * ((K j)ᴴ * K j) * V = Vᴴ * V := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hK, Matrix.mul_one]
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, s1, s2, s3]
    abel
  have := congrArg (fun T => (Matrix.trace T).re) hexp
  simp only [Matrix.trace_sum, Matrix.trace_sub, Complex.re_sum, Complex.sub_re] at this
  rw [this] at h0
  linarith

omit [DecidableEq κ] in
lemma exists_sq {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : ∃ B : Matrix ι ι ℂ, X = Bᴴ * B := by
  refine ⟨diagonal (fun a => ((Real.sqrt (hX.isHermitian.eigenvalues a) : ℝ) : ℂ)) *
    (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ, ?_⟩
  rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  conv_lhs => rw [spec_eq hX.isHermitian]
  rw [show ∀ (P D1 D2 : Matrix ι ι ℂ), P * D1 * (D2 * Pᴴ) = P * (D1 * D2) * Pᴴ from
    fun P D1 D2 => by simp only [Matrix.mul_assoc], diagonal_mul_diagonal]
  congr 3
  ext a
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hX.eigenvalues_nonneg a)]

/-- Kadison–Schwarz in trace form. -/
lemma ks_tr (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (Z : Matrix κ κ ℂ) :
    (X * (Φd K Z * (Φd K Z)ᴴ)).trace.re ≤ (X * Φd K (Z * Zᴴ)).trace.re := by
  obtain ⟨B, rfl⟩ := exists_sq hX
  have h := cs K hK (fun j => Zᴴ * K j * Bᴴ)
  have e1 : ∑ j, (K j)ᴴ * (Zᴴ * K j * Bᴴ) = (Φd K Z)ᴴ * Bᴴ := by
    simp only [Φd, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sum_mul,
      Matrix.mul_assoc]
  rw [e1] at h
  set W := Φd K Z
  have e2 : ((Wᴴ * Bᴴ)ᴴ * (Wᴴ * Bᴴ)).trace = (Bᴴ * B * (W * Wᴴ)).trace := by
    calc ((Wᴴ * Bᴴ)ᴴ * (Wᴴ * Bᴴ)).trace = ((B * W * Wᴴ) * Bᴴ).trace := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (Bᴴ * (B * W * Wᴴ)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ∑ j, ((Zᴴ * K j * Bᴴ)ᴴ * (Zᴴ * K j * Bᴴ)).trace.re = (Bᴴ * B * Φd K (Z * Zᴴ)).trace.re := by
    simp only [Φd, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    calc ((Zᴴ * K j * Bᴴ)ᴴ * (Zᴴ * K j * Bᴴ)).trace = ((B * (K j)ᴴ * Z * Zᴴ * K j) * Bᴴ).trace := by
          rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
            conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (Bᴴ * (B * (K j)ᴴ * Z * Zᴴ * K j)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e2, e3] at h
  exact h

lemma tr_dual (K : J → Matrix κ ι ℂ) (Q : Matrix κ κ ℂ) (X : Matrix ι ι ℂ) :
    (Q * Φ K X).trace = (Φd K Q * X).trace := by
  simp only [Φ, Φd, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Q * (K j * X * (K j)ᴴ) = (Q * (K j * X)) * (K j)ᴴ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma Φd_star (K : J → Matrix κ ι ℂ) (Z : Matrix κ κ ℂ) : Φd K Zᴴ = (Φd K Z)ᴴ := by
  simp only [Φd, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma val_mono (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) (Z : Matrix κ κ ℂ) :
    val A B (Φ K X) (Φ K Y) Z ≤ val A B X Y (Φd K Z) := by
  unfold val
  have t1 : (Zᴴ * Φ K X).trace = ((Φd K Z)ᴴ * X).trace := by rw [tr_dual, Φd_star]
  have t2 : (Zᴴ * Φ K X * Z).trace = (X * Φd K (Z * Zᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, tr_dual, Matrix.trace_mul_comm]
  have t2' : ((Φd K Z)ᴴ * X * Φd K Z).trace = (X * (Φd K Z * (Φd K Z)ᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have t3 : (Z * Φ K Y * Zᴴ).trace = (Y * Φd K (Zᴴ * Z)).trace := by
    rw [Matrix.trace_mul_cycle, tr_dual, Matrix.trace_mul_comm]
  have t3' : (Φd K Z * Y * (Φd K Z)ᴴ).trace = (Y * (Φd K Zᴴ * (Φd K Zᴴ)ᴴ)).trace := by
    rw [Φd_star, conjTranspose_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have k2 := ks_tr K hK hX Z
  have k3 := ks_tr K hK hY Zᴴ
  rw [conjTranspose_conjTranspose] at k3
  rw [t1, t2, t2', t3, t3']
  nlinarith [mul_le_mul_of_nonneg_left k2 hA, mul_le_mul_of_nonneg_left k3 hB]

theorem G_mono (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hX' : (Φ K X).PosSemidef) (hY' : (Φ K Y).PosSemidef)
    (hs : ∀ a b, A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b = 0 →
      (hX.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX.isHermitian hY.isHermitian a b = 0) :
    G A B hX'.isHermitian hY'.isHermitian ≤ G A B hX.isHermitian hY.isHermitian := by
  obtain ⟨Z, hZ⟩ := var_eq A B hX'.isHermitian hY'.isHermitian
  rw [← hZ]
  exact (val_mono K hK A B hA hB hX hY Z).trans (var_le A B hA hB hX hY hs _)

end X5DP
end X5mod_DP_KS

section X5mod_PQ_Int
open MeasureTheory Set Real

namespace X5PQ

noncomputable def K (p : ℝ) : ℝ := ∫ t in Ioi 0, rpowIntegrand₀₁ (p - 1) t 1

lemma K_pos {p : ℝ} (hp : p ∈ Ioo 1 2) : 0 < K p :=
  integral_rpowIntegrand₀₁_one_pos ⟨by linarith [hp.1], by linarith [hp.2]⟩

noncomputable def φ (p t x y : ℝ) : ℝ := t ^ (p - 2) * (x ^ 2 / (x + t * y))

lemma phi_eq {p t x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (ht : 0 < t) :
    y * rpowIntegrand₁₂ p t (x / y) = φ p t x y := by
  unfold rpowIntegrand₁₂ φ
  have e : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show p - 1 = (p - 2) + 1 by ring, rpow_add ht, rpow_one]
  rw [e]
  have h1 : 0 < x + t * y := by positivity
  have h2 : t + x / y ≠ 0 := by positivity
  have h3 : t + x / y = (x + t * y) / y := by field_simp; ring
  rw [h3]
  field_simp
  ring

lemma phi_int {p x y : ℝ} (hp : p ∈ Ioo 1 2) (hx : 0 ≤ x) (hy : 0 < y) :
    IntegrableOn (fun t => φ p t x y) (Ioi 0) := by
  have : IntegrableOn (fun t => y * rpowIntegrand₁₂ p t (x / y)) (Ioi 0) :=
    (integrableOn_rpowIntegrand₁₂ hp (div_nonneg hx hy.le)).const_mul y
  exact IntegrableOn.congr_fun this (fun t ht => phi_eq hx hy ht) measurableSet_Ioi

lemma persp {p x y : ℝ} (hp : p ∈ Ioo 1 2) (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ p * y ^ (1 - p) = (K p)⁻¹ * ∫ t in Ioi 0, φ p t x y := by
  have e1 : x ^ p * y ^ (1 - p) = y * (x / y) ^ p := by
    rw [div_rpow hx hy.le, rpow_sub hy, rpow_one]; field_simp
  rw [e1, rpow_eq_const_mul_integral_rpowIntegrand₁₂ hp (div_nonneg hx hy.le)]
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => phi_eq (p := p) hx hy ht),
    integral_const_mul]
  unfold K; ring

theorem int_cmp {ι κ : Type*} (S : Finset ι) (T : Finset κ) (x y : ι → ℝ) (u v c : κ → ℝ)
    {p : ℝ} (hp : p ∈ Ioo 1 2)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ S, 0 < y i) (hu : ∀ k ∈ T, 0 ≤ u k) (hv : ∀ k ∈ T, 0 < v k)
    (h : ∀ t, 0 < t → ∑ i ∈ S, x i ^ 2 / (x i + t * y i) ≤ ∑ k ∈ T, c k * (u k ^ 2 / (u k + t * v k))) :
    ∑ i ∈ S, x i ^ p * y i ^ (1 - p) ≤ ∑ k ∈ T, c k * (u k ^ p * v k ^ (1 - p)) := by
  have hL : ∑ i ∈ S, x i ^ p * y i ^ (1 - p) = (K p)⁻¹ * ∫ t in Ioi 0, ∑ i ∈ S, φ p t (x i) (y i) := by
    rw [integral_finsetSum S fun i hi => phi_int hp (hx i hi) (hy i hi), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => persp hp (hx i hi) (hy i hi)
  have hR : ∑ k ∈ T, c k * (u k ^ p * v k ^ (1 - p)) =
      (K p)⁻¹ * ∫ t in Ioi 0, ∑ k ∈ T, c k * φ p t (u k) (v k) := by
    rw [integral_finsetSum T fun k hk => (phi_int hp (hu k hk) (hv k hk)).const_mul (c k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [persp hp (hu k hk) (hv k hk), integral_const_mul]; ring
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (K_pos hp).le)
  refine setIntegral_mono_on (integrable_finsetSum S fun i hi => phi_int hp (hx i hi) (hy i hi))
    (integrable_finsetSum T fun k hk => (phi_int hp (hu k hk) (hv k hk)).const_mul (c k))
    measurableSet_Ioi fun t ht => ?_
  have h0 : 0 < t ^ (p - 2) := rpow_pos_of_pos ht _
  have := mul_le_mul_of_nonneg_left (h t ht) h0.le
  simp only [φ, Finset.mul_sum] at this ⊢
  convert this using 2 with k
  ring

end X5PQ
end X5mod_PQ_Int

section X5mod_DP_Int
open MeasureTheory Set Real

namespace X5DP

/-- generic comparison of finite sums of integral representations -/
theorem cmp_gen {ι κ : Type*} (S : Finset ι) (T : Finset κ) (x y c : ι → ℝ) (u v d : κ → ℝ)
    (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ x y : ℝ, 0 ≤ x → 0 < y → F x y = C * ∫ s in Ioi 0, φ s x y)
    (hint : ∀ x y : ℝ, 0 ≤ x → 0 < y → IntegrableOn (fun s => φ s x y) (Ioi 0))
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ S, 0 < y i) (hu : ∀ k ∈ T, 0 ≤ u k) (hv : ∀ k ∈ T, 0 < v k)
    (h : ∀ s, 0 < s → ∑ i ∈ S, c i * φ s (x i) (y i) ≤ ∑ k ∈ T, d k * φ s (u k) (v k)) :
    ∑ i ∈ S, c i * F (x i) (y i) ≤ ∑ k ∈ T, d k * F (u k) (v k) := by
  have hL : ∑ i ∈ S, c i * F (x i) (y i) = C * ∫ s in Ioi 0, ∑ i ∈ S, c i * φ s (x i) (y i) := by
    rw [integral_finsetSum S fun i hi => (hint _ _ (hx i hi) (hy i hi)).const_mul (c i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hrep _ _ (hx i hi) (hy i hi), integral_const_mul]; ring
  have hR : ∑ k ∈ T, d k * F (u k) (v k) = C * ∫ s in Ioi 0, ∑ k ∈ T, d k * φ s (u k) (v k) := by
    rw [integral_finsetSum T fun k hk => (hint _ _ (hu k hk) (hv k hk)).const_mul (d k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hrep _ _ (hu k hk) (hv k hk), integral_const_mul]; ring
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact setIntegral_mono_on
    (integrable_finsetSum S fun i hi => (hint _ _ (hx i hi) (hy i hi)).const_mul (c i))
    (integrable_finsetSum T fun k hk => (hint _ _ (hu k hk) (hv k hk)).const_mul (d k))
    measurableSet_Ioi h

/-- integrand for `p ∈ (0,1)` -/
noncomputable def φ0 (p s x y : ℝ) : ℝ := s ^ (p - 1) * y - s ^ p * (y ^ 2 / (x + s * y))

lemma phi0_eq {p s x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hs : 0 < s) :
    y * rpowIntegrand₀₁ p s (x / y) = φ0 p s x y := by
  unfold rpowIntegrand₀₁ φ0
  have e : s ^ (p - 1) = s ^ p * s⁻¹ := by rw [rpow_sub_one hs.ne', div_eq_mul_inv]
  rw [e]
  have h1 : 0 < x + s * y := by positivity
  have h3 : s + x / y = (x + s * y) / y := by field_simp; ring
  rw [h3]
  field_simp

lemma phi0_int {p x y : ℝ} (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hy : 0 < y) :
    IntegrableOn (fun s => φ0 p s x y) (Ioi 0) := by
  have : IntegrableOn (fun s => y * rpowIntegrand₀₁ p s (x / y)) (Ioi 0) :=
    (integrableOn_rpowIntegrand₀₁_Ioi hp (div_nonneg hx hy.le)).const_mul y
  exact IntegrableOn.congr_fun this (fun s hs => phi0_eq hx hy hs) measurableSet_Ioi

lemma persp0 {p x y : ℝ} (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ p * y ^ (1 - p) = (∫ s in Ioi 0, rpowIntegrand₀₁ p s 1)⁻¹ * ∫ s in Ioi 0, φ0 p s x y := by
  have e1 : x ^ p * y ^ (1 - p) = y * (x / y) ^ p := by
    rw [div_rpow hx hy.le, rpow_sub hy, rpow_one]; field_simp
  rw [e1, rpow_eq_const_mul_integral hp (div_nonneg hx hy.le)]
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun s hs => phi0_eq (p := p) hx hy hs),
    integral_const_mul]
  ring

lemma K0_pos {p : ℝ} (hp : p ∈ Ioo 0 1) : 0 < ∫ s in Ioi 0, rpowIntegrand₀₁ p s 1 :=
  integral_rpowIntegrand₀₁_one_pos hp

end X5DP
end X5mod_DP_Int

section X5mod_DP_Q
open Matrix MeasureTheory Set
open scoped ComplexOrder

namespace X5DP

variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype J]

lemma Φ_psd (K : J → Matrix κ ι ℂ) {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : (Φ K X).PosSemidef :=
  Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (K j)

lemma Φ_tr (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (X : Matrix ι ι ℂ) :
    (Φ K X).trace = X.trace := by
  have := tr_dual K 1 X
  rw [Matrix.one_mul] at this
  rw [this]
  simp only [Φd, Matrix.mul_one, hK, Matrix.one_mul]

lemma Φ_supp (K : J → Matrix κ ι ℂ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    LinearMap.ker (Φ K Y).mulVecLin ≤ LinearMap.ker (Φ K X).mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have hq : ∀ j, star ((K j)ᴴ *ᵥ v) ⬝ᵥ Y *ᵥ ((K j)ᴴ *ᵥ v) = 0 := by
    have h0 : star v ⬝ᵥ (Φ K Y) *ᵥ v = 0 := by rw [hv, dotProduct_zero]
    have e : star v ⬝ᵥ (Φ K Y) *ᵥ v = ∑ j, star ((K j)ᴴ *ᵥ v) ⬝ᵥ Y *ᵥ ((K j)ᴴ *ᵥ v) := by
      simp only [Φ, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
      try rfl
    have hn : ∀ j, 0 ≤ star ((K j)ᴴ *ᵥ v) ⬝ᵥ Y *ᵥ ((K j)ᴴ *ᵥ v) := fun j => hY.dotProduct_mulVec_nonneg _
    rw [e] at h0
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn j).1 h0 j (Finset.mem_univ j)
  have hX0 : ∀ j, X *ᵥ ((K j)ᴴ *ᵥ v) = 0 := by
    intro j
    have h1 := (hY.dotProduct_mulVec_zero_iff _).1 (hq j)
    have := hs (show (K j)ᴴ *ᵥ v ∈ LinearMap.ker Y.mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply]; exact h1)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  simp only [Φ, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, hX0, mulVec_zero]

/-- Petz quasi-entropy with support convention. -/
noncomputable def Qf (t : ℝ) (X Y : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ t) X * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) Y).trace.re

lemma w_swap {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (a b : ι) :
    X5OL.w hY hX b a = X5OL.w hX hY a b := by
  have : X5OL.ov hY hX = (X5OL.ov hX hY)ᴴ := by
    simp [X5OL.ov, star_eq_conjTranspose, conjTranspose_mul]
  simp only [X5OL.w, this, conjTranspose_apply, norm_star]

lemma w_col {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (b : ι) :
    ∑ a, X5OL.w hX hY a b = 1 := by
  rw [← X5OL.w_row hY hX b]
  exact Finset.sum_congr rfl fun a _ => (w_swap hX hY a b).symm

/-- pair-sum over `μ ≠ 0` -/
noncomputable def Tset {X Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) : Finset (ι × ι) :=
  Finset.univ.filter fun k => hY.eigenvalues k.2 ≠ 0

lemma Qf_sum (t : ℝ) (ht : 1 - t ≠ 0) {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Qf t X Y = ∑ k ∈ Tset (X := X) hY, X5OL.w hX hY k.1 k.2 *
      (hX.eigenvalues k.1 ^ t * hY.eigenvalues k.2 ^ (1 - t)) := by
  unfold Qf
  rw [X5OL.tr_cfc_cfc hX hY, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [← Fintype.sum_prod_type' (f := fun a b => hX.eigenvalues a ^ t *
    (if hY.eigenvalues b = 0 then 0 else hY.eigenvalues b ^ (1 - t)) * X5OL.w hX hY a b)]
  unfold Tset
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : hY.eigenvalues k.2 = 0
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, if_true]; ring

lemma G_sum (A B : ℝ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (h0 : ∀ a b, hY.isHermitian.eigenvalues b = 0 →
      X5OL.w hX.isHermitian hY.isHermitian a b * hX.isHermitian.eigenvalues a ^ 2 /
        (A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b) = 0) :
    G A B hX.isHermitian hY.isHermitian = ∑ k ∈ Tset (X := X) hY.isHermitian,
      X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 * (hX.isHermitian.eigenvalues k.1 ^ 2 /
        (A * hX.isHermitian.eigenvalues k.1 + B * hY.isHermitian.eigenvalues k.2)) := by
  unfold G Tset
  rw [← Fintype.sum_prod_type' (f := fun a b => X5OL.w hX.isHermitian hY.isHermitian a b *
    hX.isHermitian.eigenvalues a ^ 2 / (A * hX.isHermitian.eigenvalues a +
      B * hY.isHermitian.eigenvalues b)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · ring
  · rw [h0 k.1 k.2 (not_not.1 h)]

lemma hz {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) (a b : ι)
    (hb : hY.isHermitian.eigenvalues b = 0) :
    X5OL.w hX.isHermitian hY.isHermitian a b * hX.isHermitian.eigenvalues a ^ 2 = 0 := by
  by_cases ha : hX.isHermitian.eigenvalues a = 0
  · simp [ha]
  · simp [X5OL.w, X5OL.supp_fwd hX.isHermitian hY.isHermitian hs a b ha hb]

lemma Tpos {X Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) (k : ι × ι) (hk : k ∈ Tset (X := X) hY.isHermitian) :
    0 < hY.isHermitian.eigenvalues k.2 :=
  lt_of_le_of_ne (hY.eigenvalues_nonneg _) (Finset.mem_filter.1 hk).2.symm

lemma Qf2_eq {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Qf 2 X Y = G 0 1 hX.isHermitian hY.isHermitian := by
  unfold Qf G
  rw [X5OL.tr_cfc_cfc hX.isHermitian hY.isHermitian, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.ofReal_re, zero_mul, one_mul, zero_add, Real.rpow_two]
  norm_num
  split_ifs with h
  · simp [h]
  · rw [Real.rpow_neg_one]; field_simp

theorem Qf_gt (t : ℝ) (h1 : 1 < t) (h2 : t ≤ 2) (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    Qf t (Φ K X) (Φ K Y) ≤ Qf t X Y := by
  have hX' := Φ_psd K hX
  have hY' := Φ_psd K hY
  have hs' := Φ_supp K hX hY hs
  have hne : 1 - t ≠ 0 := by linarith
  rcases h2.lt_or_eq with h2 | h2
  · rw [Qf_sum t hne hX'.isHermitian hY'.isHermitian, Qf_sum t hne hX.isHermitian hY.isHermitian]
    refine cmp_gen _ _ _ _ _ _ _ _ (fun x y => x ^ t * y ^ (1 - t)) (X5PQ.φ t) (X5PQ.K t)⁻¹
      (inv_nonneg.2 (X5PQ.K_pos ⟨h1, h2⟩).le) (fun x y hx hy => X5PQ.persp ⟨h1, h2⟩ hx hy)
      (fun x y hx hy => X5PQ.phi_int ⟨h1, h2⟩ hx hy)
      (fun k _ => hX'.eigenvalues_nonneg _) (fun k hk => Tpos hY' k hk)
      (fun k _ => hX.eigenvalues_nonneg _) (fun k hk => Tpos hY k hk) fun s hs0 => ?_
    have hG := G_mono K hK 1 s zero_le_one hs0.le hX hY hX' hY' (fun a b h0 => by
      have : hX.isHermitian.eigenvalues a = 0 := by
        nlinarith [hX.eigenvalues_nonneg a, mul_nonneg hs0.le (hY.eigenvalues_nonneg b)]
      simp [this])
    rw [G_sum 1 s hX' hY' (fun a b hb => by rw [hz hX' hY' hs' a b hb, zero_div]),
      G_sum 1 s hX hY (fun a b hb => by rw [hz hX hY hs a b hb, zero_div])] at hG
    have hpos : 0 ≤ s ^ (t - 2) := Real.rpow_nonneg hs0.le _
    have := mul_le_mul_of_nonneg_left hG hpos
    simp only [Finset.mul_sum, one_mul] at this
    simp only [X5PQ.φ]
    convert this using 2 <;> first | rfl | ring
  · subst h2
    rw [Qf2_eq hX' hY', Qf2_eq hX hY]
    exact G_mono K hK 0 1 le_rfl zero_le_one hX hY hX' hY' fun a b h0 => by
      have hb : hY.isHermitian.eigenvalues b = 0 := by linarith
      by_cases ha : hX.isHermitian.eigenvalues a = 0
      · simp [ha]
      · simp [X5OL.supp_fwd hX.isHermitian hY.isHermitian hs a b ha hb]

lemma sumT_mu {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ k ∈ Tset (X := X) hY, X5OL.w hX hY k.1 k.2 * hY.eigenvalues k.2 = Y.trace.re := by
  unfold Tset
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (g := fun k : ι × ι => X5OL.w hX hY k.1 k.2 * hY.eigenvalues k.2)
    (fun k _ => by split_ifs with h <;> simp_all)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hY.trace_eq_sum_eigenvalues, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [← Finset.sum_mul, w_col, one_mul]
  simp

lemma sumT_H (s : ℝ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∑ k ∈ Tset (X := X) hY.isHermitian, X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
      (hY.isHermitian.eigenvalues k.2 ^ 2 /
        (hX.isHermitian.eigenvalues k.1 + s * hY.isHermitian.eigenvalues k.2)) =
      G s 1 hY.isHermitian hX.isHermitian := by
  unfold Tset G
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (g := fun k : ι × ι => X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
      (hY.isHermitian.eigenvalues k.2 ^ 2 /
        (hX.isHermitian.eigenvalues k.1 + s * hY.isHermitian.eigenvalues k.2)))
    (fun k _ => by split_ifs with h <;> simp_all)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [w_swap]; ring

lemma key0 (t s : ℝ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∑ k ∈ Tset (X := X) hY.isHermitian, X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
        φ0 t s (hX.isHermitian.eigenvalues k.1) (hY.isHermitian.eigenvalues k.2) =
      s ^ (t - 1) * Y.trace.re - s ^ t * G s 1 hY.isHermitian hX.isHermitian := by
  rw [← sumT_mu hX.isHermitian hY.isHermitian, ← sumT_H s hX hY, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold φ0; ring

theorem Qf_lt (t : ℝ) (h0 : 0 < t) (h1 : t < 1) (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Qf t X Y ≤ Qf t (Φ K X) (Φ K Y) := by
  have hX' := Φ_psd K hX
  have hY' := Φ_psd K hY
  have hne : 1 - t ≠ 0 := by linarith
  rw [Qf_sum t hne hX'.isHermitian hY'.isHermitian, Qf_sum t hne hX.isHermitian hY.isHermitian]
  refine cmp_gen _ _ _ _ _ _ _ _ (fun x y => x ^ t * y ^ (1 - t)) (φ0 t)
    (∫ s in Ioi 0, Real.rpowIntegrand₀₁ t s 1)⁻¹ (inv_nonneg.2 (K0_pos ⟨h0, h1⟩).le)
    (fun x y hx hy => persp0 ⟨h0, h1⟩ hx hy) (fun x y hx hy => phi0_int ⟨h0, h1⟩ hx hy)
    (fun k _ => hX.eigenvalues_nonneg _) (fun k hk => Tpos hY k hk)
    (fun k _ => hX'.eigenvalues_nonneg _) (fun k hk => Tpos hY' k hk) fun s hs0 => ?_
  have hG := G_mono K hK s 1 hs0.le zero_le_one hY hX hY' hX' (fun a b h0 => by
    have : hY.isHermitian.eigenvalues a = 0 := by
      nlinarith [hY.eigenvalues_nonneg a, hX.eigenvalues_nonneg b, mul_nonneg hs0.le (hY.eigenvalues_nonneg a)]
    simp [this])
  rw [key0 t s hX hY, key0 t s hX' hY', Φ_tr K hK]
  have hpos : 0 ≤ s ^ t := Real.rpow_nonneg hs0.le _
  nlinarith [mul_le_mul_of_nonneg_left hG hpos]

end X5DP
end X5mod_DP_Q

section X5mod_RM_Gen
open Matrix MeasureTheory Set
open scoped ComplexOrder

namespace X5RM
open X5DP

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tr_psd_nonneg {X D : Matrix ι ι ℂ} (hX : X.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (X * D).trace.re := by
  obtain ⟨B, rfl⟩ := exists_sq hX
  have h : (Bᴴ * B * D).trace = (B * D * Bᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h]
  have := (hD.mul_mul_conjTranspose_same B).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

variable (E : Matrix ι ι ℂ → Matrix κ κ ℂ) (Ed : Matrix κ κ ℂ → Matrix ι ι ℂ)

/-- Hypotheses: `Ed` is the trace dual of `E`, star-preserving, unital and Schwarz. -/
structure Pair : Prop where
  htr : ∀ Q X, (Q * E X).trace = (Ed Q * X).trace
  hst : ∀ Z, Ed Zᴴ = (Ed Z)ᴴ
  hks : ∀ Z, (Ed (Z * Zᴴ) - Ed Z * (Ed Z)ᴴ).PosSemidef
  hu : Ed 1 = 1
  hpsd : ∀ X, X.PosSemidef → (E X).PosSemidef

variable {E Ed}

lemma ks_tr (hP : Pair E Ed) {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (Z : Matrix κ κ ℂ) :
    (X * (Ed Z * (Ed Z)ᴴ)).trace.re ≤ (X * Ed (Z * Zᴴ)).trace.re := by
  have := tr_psd_nonneg hX (hP.hks Z)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma E_tr (hP : Pair E Ed) (X : Matrix ι ι ℂ) : (E X).trace = X.trace := by
  have := hP.htr 1 X
  rw [Matrix.one_mul, hP.hu, Matrix.one_mul] at this
  exact this

lemma val_mono (hP : Pair E Ed) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) (Z : Matrix κ κ ℂ) :
    val A B (E X) (E Y) Z ≤ val A B X Y (Ed Z) := by
  unfold val
  have t1 : (Zᴴ * E X).trace = ((Ed Z)ᴴ * X).trace := by rw [hP.htr, hP.hst]
  have t2 : (Zᴴ * E X * Z).trace = (X * Ed (Z * Zᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, hP.htr, Matrix.trace_mul_comm]
  have t2' : ((Ed Z)ᴴ * X * Ed Z).trace = (X * (Ed Z * (Ed Z)ᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have t3 : (Z * E Y * Zᴴ).trace = (Y * Ed (Zᴴ * Z)).trace := by
    rw [Matrix.trace_mul_cycle, hP.htr, Matrix.trace_mul_comm]
  have t3' : (Ed Z * Y * (Ed Z)ᴴ).trace = (Y * (Ed Zᴴ * (Ed Zᴴ)ᴴ)).trace := by
    rw [hP.hst, conjTranspose_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have k2 := ks_tr hP hX Z
  have k3 := ks_tr hP hY Zᴴ
  rw [conjTranspose_conjTranspose] at k3
  rw [t1, t2, t2', t3, t3']
  nlinarith [mul_le_mul_of_nonneg_left k2 hA, mul_le_mul_of_nonneg_left k3 hB]

theorem G_mono (hP : Pair E Ed) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hX' : (E X).PosSemidef) (hY' : (E Y).PosSemidef)
    (hs : ∀ a b, A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b = 0 →
      (hX.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX.isHermitian hY.isHermitian a b = 0) :
    G A B hX'.isHermitian hY'.isHermitian ≤ G A B hX.isHermitian hY.isHermitian := by
  obtain ⟨Z, hZ⟩ := var_eq A B hX'.isHermitian hY'.isHermitian
  rw [← hZ]
  exact (val_mono hP A B hA hB hX hY Z).trans (var_le A B hA hB hX hY hs _)

theorem Qf_lt (hP : Pair E Ed) (t : ℝ) (h0 : 0 < t) (h1 : t < 1)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Qf t X Y ≤ Qf t (E X) (E Y) := by
  have hX' := hP.hpsd X hX
  have hY' := hP.hpsd Y hY
  have hne : 1 - t ≠ 0 := by linarith
  rw [Qf_sum t hne hX'.isHermitian hY'.isHermitian, Qf_sum t hne hX.isHermitian hY.isHermitian]
  refine cmp_gen _ _ _ _ _ _ _ _ (fun x y => x ^ t * y ^ (1 - t)) (φ0 t)
    (∫ s in Ioi 0, Real.rpowIntegrand₀₁ t s 1)⁻¹ (inv_nonneg.2 (K0_pos ⟨h0, h1⟩).le)
    (fun x y hx hy => persp0 ⟨h0, h1⟩ hx hy) (fun x y hx hy => phi0_int ⟨h0, h1⟩ hx hy)
    (fun k _ => hX.eigenvalues_nonneg _) (fun k hk => Tpos hY k hk)
    (fun k _ => hX'.eigenvalues_nonneg _) (fun k hk => Tpos hY' k hk) fun s hs0 => ?_
  have hG := G_mono hP s 1 hs0.le zero_le_one hY hX hY' hX' (fun a b h0 => by
    have : hY.isHermitian.eigenvalues a = 0 := by
      nlinarith [hY.eigenvalues_nonneg a, hX.eigenvalues_nonneg b, mul_nonneg hs0.le (hY.eigenvalues_nonneg a)]
    simp [this])
  rw [key0 t s hX hY, key0 t s hX' hY', E_tr hP]
  have hpos : 0 ≤ s ^ t := Real.rpow_nonneg hs0.le _
  nlinarith [mul_le_mul_of_nonneg_left hG hpos]

end X5RM
end X5mod_RM_Gen

section X5mod_RM_Thm
open Matrix Set
open scoped ComplexOrder

namespace X5RM
open X5DP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma tr_psd_nonneg' {X D : Matrix J J ℂ} (hX : X.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (X * D).trace := by
  obtain ⟨B, rfl⟩ := exists_sq hX
  have h : (Bᴴ * B * D).trace = (B * D * Bᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h]; exact (hD.mul_mul_conjTranspose_same B).trace_nonneg

section
variable (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hS : Schwarz Phi)
include hS

lemma phi_psd {P : Matrix I I ℂ} (hP : P.PosSemidef) : (Phi P).PosSemidef := by
  obtain ⟨B, rfl⟩ := exists_sq hP
  have h1 : (Phi (Bᴴ * B) - (Phi B)ᴴ * Phi B).PosSemidef := hS B
  have := h1.add (posSemidef_conjTranspose_mul_self (Phi B))
  rwa [sub_add_cancel] at this

lemma phi_herm {H : Matrix I I ℂ} (hH : H.IsHermitian) : (Phi H).IsHermitian := by
  have e : H = (1 / 4 : ℂ) • ((H + 1)ᴴ * (H + 1) - (H - 1)ᴴ * (H - 1)) := by
    rw [conjTranspose_add, conjTranspose_sub, conjTranspose_one, hH.eq]
    have : (H + 1) * (H + 1) - (H - 1) * (H - 1) = (4 : ℂ) • H := by
      rw [show (4 : ℂ) • H = H + H + H + H by
        rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num]; simp only [add_smul, one_smul]]
      noncomm_ring
    rw [this, smul_smul]; norm_num
  have h1 := (phi_psd Phi hS (posSemidef_conjTranspose_mul_self (H + 1))).1
  have h2 := (phi_psd Phi hS (posSemidef_conjTranspose_mul_self (H - 1))).1
  rw [e, map_smul, map_sub]
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, h1.eq, h2.eq]
  congr 1
  simp [Complex.ext_iff]

lemma phi_star (Z : Matrix I I ℂ) : Phi Zᴴ = (Phi Z)ᴴ := by
  obtain ⟨H1, H2, k1, k2, e1, e2⟩ : ∃ H1 H2 : Matrix I I ℂ, H1.IsHermitian ∧ H2.IsHermitian ∧
      Zᴴ = (1 / 2 : ℂ) • (H1 + Complex.I • H2) ∧ Z = (1 / 2 : ℂ) • (H1 - Complex.I • H2) := by
    refine ⟨Z + Zᴴ, Complex.I • (Z - Zᴴ), ?_, ?_, ?_, ?_⟩
    · unfold IsHermitian; simp only [conjTranspose_add, conjTranspose_conjTranspose]; abel
    · unfold IsHermitian
      simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      rw [show star Complex.I = -Complex.I by simp, neg_smul, ← smul_neg, neg_sub]
    · ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring_nf; simp only [Complex.I_sq]; ring
    · ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring_nf; simp only [Complex.I_sq]; ring
  have h1 := phi_herm Phi hS k1
  have h2 := phi_herm Phi hS k2
  conv_lhs => rw [e1]
  conv_rhs => rw [e2]
  simp only [map_smul, map_add, map_sub]
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_smul, h1.eq, h2.eq]
  have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp [Complex.ext_iff]
  rw [s1, show star Complex.I = -Complex.I by simp, neg_smul, sub_neg_eq_add]

lemma pb_tr (Q : Matrix I I ℂ) (X : Matrix J J ℂ) :
    (Q * pullback Phi X).trace = (Phi Q * X).trace := by
  conv_rhs => rw [matrix_eq_sum_single Q]
  have hs : ∀ i j, single i j (Q i j) = (Q i j) • single i j (1 : ℂ) := by
    intro i j; rw [smul_single, smul_eq_mul, mul_one]
  simp only [hs, map_sum, map_smul, Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.trace, diag_apply, mul_apply, pullback]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := Matrix.trace_mul_comm X (Phi (single i j 1))
  simp only [Matrix.trace, diag_apply] at this
  exact this

lemma pb_psd {X : Matrix J J ℂ} (hX : X.PosSemidef) : (pullback Phi X).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · ext i j
    simp only [conjTranspose_apply, pullback]
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hX.1.eq, ← phi_star Phi hS,
      conjTranspose_single, star_one, Matrix.trace_mul_comm]
  · have e : star v ⬝ᵥ (pullback Phi X *ᵥ v) = (vecMulVec v (star v) * pullback Phi X).trace := by
      simp only [dotProduct, mulVec, Matrix.trace, diag_apply, mul_apply, vecMulVec_apply,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.star_apply]; ring
    rw [e, pb_tr Phi hS, Matrix.trace_mul_comm]
    exact tr_psd_nonneg' hX (phi_psd Phi hS (posSemidef_vecMulVec_self_star v))

lemma pair (hu : Phi 1 = 1) : Pair (pullback Phi) Phi where
  htr := pb_tr Phi hS
  hst := phi_star Phi hS
  hks Z := by
    have h : (Phi (Zᴴᴴ * Zᴴ) - (Phi Zᴴ)ᴴ * Phi Zᴴ).PosSemidef := hS Zᴴ
    rwa [conjTranspose_conjTranspose, phi_star Phi hS, conjTranspose_conjTranspose] at h
  hu := hu
  hpsd _ hX := pb_psd Phi hS hX

end

/-- the Rényi overlap as a function of the exponent -/
noncomputable def S (X Y : Matrix J J ℂ) (t : ℝ) : ℝ := ev (supportPower X t) (supportPower Y (1 - t))

lemma S_eq {X Y : Matrix J J ℂ} {t : ℝ} (ht : 0 < t) : S X Y t = Qf t X Y := by
  unfold S ev QAlgorithms.effectProb Qf supportPower
  rw [Matrix.trace_mul_comm]
  congr 4
  funext x
  by_cases hx : x = 0
  · simp [hx, Real.zero_rpow ht.ne']
  · simp [hx]

lemma cp (μ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun t => if μ = 0 then (0 : ℝ) else Real.rpow μ (f t) := by
  by_cases h : μ = 0
  · simp only [h, if_true]; exact continuous_const
  · simp only [h, if_false]
    exact Continuous.rpow continuous_const hf fun _ => Or.inl h

lemma S_sum {X Y : Matrix J J ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    S X Y = fun t => ∑ i, ∑ j, ((if hY.eigenvalues i = 0 then 0 else
      Real.rpow (hY.eigenvalues i) (1 - t)) * (if hX.eigenvalues j = 0 then 0 else
      Real.rpow (hX.eigenvalues j) t) * X5OL.w hY hX i j) := by
  funext t
  unfold S ev QAlgorithms.effectProb supportPower
  rw [X5OL.tr_cfc_cfc hY hX, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]

lemma S_cont {X Y : Matrix J J ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Continuous (S X Y) := by
  rw [S_sum hX hY]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((cp _ (continuous_const.sub continuous_id)).mul (cp _ continuous_id)).mul continuous_const

lemma S_nonneg {X Y : Matrix J J ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) (t : ℝ) :
    0 ≤ S X Y t := by
  rw [S_sum hX.1 hY.1]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg (mul_nonneg ?_ ?_) (X5OL.w_nonneg _ _ _ _)
  · split_ifs; exact le_rfl; exact Real.rpow_nonneg (hY.eigenvalues_nonneg _) _
  · split_ifs; exact le_rfl; exact Real.rpow_nonneg (hX.eigenvalues_nonneg _) _

theorem main [Nonempty I] [Nonempty J] (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hunital : Phi 1 = 1) (hschwarz : Schwarz Phi)
    (rho nu : Matrix J J ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hnu : QAlgorithms.IsDensityMatrix nu)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    renyi rho nu a ≤ renyi (pullback Phi rho) (pullback Phi nu) a := by
  have hP := pair Phi hschwarz hunital
  have hr' := pb_psd Phi hschwarz hrho.1
  have hn' := pb_psd Phi hschwarz hnu.1
  have key : Icc (0 : ℝ) 1 ⊆ {t | S rho nu t ≤ S (pullback Phi rho) (pullback Phi nu) t} := by
    have hc : IsClosed {t | S rho nu t ≤ S (pullback Phi rho) (pullback Phi nu) t} :=
      isClosed_le (S_cont hrho.1.1 hnu.1.1) (S_cont hr'.1 hn'.1)
    have hsub : Ioo (0 : ℝ) 1 ⊆ {t | S rho nu t ≤ S (pullback Phi rho) (pullback Phi nu) t} := by
      intro t ht
      simp only [mem_ofPred_eq]
      rw [S_eq ht.1, S_eq ht.1]
      exact Qf_lt hP t ht.1 ht.2 hrho.1 hnu.1
    have := closure_minimal hsub hc
    rwa [closure_Ioo zero_ne_one] at this
  exact ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (key ha))

end X5RM
end X5mod_RM_Thm

section X5mod_RM_JC
open Matrix MeasureTheory Set
open scoped ComplexOrder

namespace X5RM
open X5DP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- convex combination -/
noncomputable def mix (u : ℝ) (X X' : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (u : ℂ) • X + ((1 - u : ℝ) : ℂ) • X'

lemma mix_psd {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {X X' : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (hX' : X'.PosSemidef) : (mix u X X').PosSemidef :=
  (hX.smul (Complex.zero_le_real.2 hu.1)).add (hX'.smul (Complex.zero_le_real.2 (by linarith [hu.2])))

lemma tr_mix (u : ℝ) (X X' : Matrix ι ι ℂ) :
    (mix u X X').trace.re = u * X.trace.re + (1 - u) * X'.trace.re := by
  simp [mix, Matrix.trace_add, Matrix.trace_smul]

lemma val_mix (A B u : ℝ) (X X' Y Y' Z : Matrix ι ι ℂ) :
    val A B (mix u X X') (mix u Y Y') Z = u * val A B X Y Z + (1 - u) * val A B X' Y' Z := by
  simp only [val, mix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
  ring

lemma G_convex (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    {X X' Y Y' : Matrix ι ι ℂ} (hX : X.PosSemidef) (hX' : X'.PosSemidef) (hY : Y.PosSemidef)
    (hY' : Y'.PosSemidef)
    (hs : ∀ a b, A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b = 0 →
      (hX.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX.isHermitian hY.isHermitian a b = 0)
    (hs' : ∀ a b, A * hX'.isHermitian.eigenvalues a + B * hY'.isHermitian.eigenvalues b = 0 →
      (hX'.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX'.isHermitian hY'.isHermitian a b = 0) :
    G A B (mix_psd hu hX hX').isHermitian (mix_psd hu hY hY').isHermitian ≤
      u * G A B hX.isHermitian hY.isHermitian + (1 - u) * G A B hX'.isHermitian hY'.isHermitian := by
  obtain ⟨Z, hZ⟩ := var_eq A B (mix_psd hu hX hX').isHermitian (mix_psd hu hY hY').isHermitian
  rw [← hZ, val_mix]
  have h1 := var_le A B hA hB hX hY hs Z
  have h2 := var_le A B hA hB hX' hY' hs' Z
  have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hu.1, mul_le_mul_of_nonneg_left h2 hu1]

lemma hs_of {s : ℝ} (hs0 : 0 < s) {X Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) (hX : X.PosSemidef) :
    ∀ a b, s * hY.isHermitian.eigenvalues a + 1 * hX.isHermitian.eigenvalues b = 0 →
      (hY.isHermitian.eigenvalues a : ℂ) * X5OL.ov hY.isHermitian hX.isHermitian a b = 0 := by
  intro a b h0
  have : hY.isHermitian.eigenvalues a = 0 := by
    nlinarith [hY.eigenvalues_nonneg a, hX.eigenvalues_nonneg b, mul_nonneg hs0.le (hY.eigenvalues_nonneg a)]
  simp [this]

theorem Qf_concave (t : ℝ) (h0 : 0 < t) (h1 : t < 1) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    {X X' Y Y' : Matrix ι ι ℂ} (hX : X.PosSemidef) (hX' : X'.PosSemidef) (hY : Y.PosSemidef)
    (hY' : Y'.PosSemidef) :
    u * Qf t X Y + (1 - u) * Qf t X' Y' ≤ Qf t (mix u X X') (mix u Y Y') := by
  have hM := mix_psd hu hX hX'
  have hN := mix_psd hu hY hY'
  have hne : 1 - t ≠ 0 := by linarith
  have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
  rw [Qf_sum t hne hM.isHermitian hN.isHermitian, Qf_sum t hne hX.isHermitian hY.isHermitian,
    Qf_sum t hne hX'.isHermitian hY'.isHermitian, Finset.mul_sum, Finset.mul_sum]
  set S1 := Tset (X := X) hY.isHermitian
  set S2 := Tset (X := X') hY'.isHermitian
  let x : (ι × ι) ⊕ (ι × ι) → ℝ := Sum.elim (fun k => hX.isHermitian.eigenvalues k.1)
    (fun k => hX'.isHermitian.eigenvalues k.1)
  let y : (ι × ι) ⊕ (ι × ι) → ℝ := Sum.elim (fun k => hY.isHermitian.eigenvalues k.2)
    (fun k => hY'.isHermitian.eigenvalues k.2)
  let c : (ι × ι) ⊕ (ι × ι) → ℝ := Sum.elim (fun k => u * X5OL.w hX.isHermitian hY.isHermitian k.1 k.2)
    (fun k => (1 - u) * X5OL.w hX'.isHermitian hY'.isHermitian k.1 k.2)
  have hsplit : ∀ F : ℝ → ℝ → ℝ, ∑ i ∈ S1.disjSum S2, c i * F (x i) (y i) =
      ∑ k ∈ S1, u * (X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
        F (hX.isHermitian.eigenvalues k.1) (hY.isHermitian.eigenvalues k.2)) +
      ∑ k ∈ S2, (1 - u) * (X5OL.w hX'.isHermitian hY'.isHermitian k.1 k.2 *
        F (hX'.isHermitian.eigenvalues k.1) (hY'.isHermitian.eigenvalues k.2)) := by
    intro F
    rw [Finset.sum_disjSum]
    simp only [c, x, y, Sum.elim_inl, Sum.elim_inr, mul_assoc]
  rw [← hsplit (fun x y => x ^ t * y ^ (1 - t))]
  refine cmp_gen _ _ x y c _ _ _ (fun x y => x ^ t * y ^ (1 - t)) (φ0 t)
    (∫ s in Ioi 0, Real.rpowIntegrand₀₁ t s 1)⁻¹ (inv_nonneg.2 (K0_pos ⟨h0, h1⟩).le)
    (fun x y hx hy => persp0 ⟨h0, h1⟩ hx hy) (fun x y hx hy => phi0_int ⟨h0, h1⟩ hx hy)
    ?_ ?_ (fun k _ => hM.eigenvalues_nonneg _) (fun k hk => Tpos hN k hk) fun s hs0 => ?_
  · intro i _
    cases i with
    | inl k => exact hX.eigenvalues_nonneg _
    | inr k => exact hX'.eigenvalues_nonneg _
  · intro i hi
    rcases Finset.mem_disjSum.1 hi with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact Tpos hY k hk
    · exact Tpos hY' k hk
  rw [hsplit (φ0 t s), ← Finset.mul_sum, ← Finset.mul_sum, key0 t s hX hY, key0 t s hX' hY',
    key0 t s hM hN, tr_mix]
  have hG := G_convex s 1 hs0.le zero_le_one hu hY hY' hX hX' (hs_of hs0 hY hX) (hs_of hs0 hY' hX')
  have hpos : 0 ≤ s ^ t := Real.rpow_nonneg hs0.le _
  nlinarith [mul_le_mul_of_nonneg_left hG hpos]

lemma log_mix {x x' y u : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hu : u ∈ Icc (0 : ℝ) 1)
    (h : u * x + (1 - u) * x' ≤ y) :
    (u : EReal) * ENNReal.log (ENNReal.ofReal x) + ((1 - u : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal x') ≤
      ENNReal.log (ENNReal.ofReal y) := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · subst h0
    simp only [EReal.coe_zero, zero_mul, zero_add, sub_zero, EReal.coe_one, one_mul] at h ⊢
    exact ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (by linarith))
  rcases eq_or_lt_of_le hu.2 with h1 | h1
  · subst h1
    simp only [sub_self, EReal.coe_zero, zero_mul, add_zero, EReal.coe_one, one_mul] at h ⊢
    exact ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (by linarith))
  have hv : 0 < 1 - u := by linarith
  rcases eq_or_lt_of_le hx with e | e
  · subst e
    rw [ENNReal.ofReal_zero, ENNReal.log_zero, EReal.coe_mul_bot_of_pos h0, EReal.bot_add]
    exact bot_le
  rcases eq_or_lt_of_le hx' with e' | e'
  · subst e'
    rw [ENNReal.ofReal_zero, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hv, EReal.add_bot]
    exact bot_le
  have hy : 0 < y := by nlinarith
  rw [ENNReal.log_ofReal_of_pos e, ENNReal.log_ofReal_of_pos e', ENNReal.log_ofReal_of_pos hy,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (mem_Ioi.2 e) (mem_Ioi.2 e') h0.le hv.le
    (by ring)
  simp only [smul_eq_mul] at hc
  exact hc.trans (Real.log_le_log (by nlinarith) h)

theorem joint (rho rhoAlt nu nuAlt : Matrix ι ι ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hrhoAlt : QAlgorithms.IsDensityMatrix rhoAlt)
    (hnu : QAlgorithms.IsDensityMatrix nu) (hnuAlt : QAlgorithms.IsDensityMatrix nuAlt)
    (a u : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (u : EReal) * renyi rho nu a + ((1-u : ℝ) : EReal) * renyi rhoAlt nuAlt a ≤
      renyi ((u : ℂ) • rho + ((1-u : ℝ) : ℂ) • rhoAlt)
        ((u : ℂ) • nu + ((1-u : ℝ) : ℂ) • nuAlt) a := by
  have hM := mix_psd hu hrho.1 hrhoAlt.1
  have hN := mix_psd hu hnu.1 hnuAlt.1
  have key : Icc (0 : ℝ) 1 ⊆ {t | u * S rho nu t + (1 - u) * S rhoAlt nuAlt t ≤
      S (mix u rho rhoAlt) (mix u nu nuAlt) t} := by
    have hc : IsClosed {t | u * S rho nu t + (1 - u) * S rhoAlt nuAlt t ≤
        S (mix u rho rhoAlt) (mix u nu nuAlt) t} :=
      isClosed_le (((S_cont hrho.1.1 hnu.1.1).const_mul u).add
        ((S_cont hrhoAlt.1.1 hnuAlt.1.1).const_mul (1 - u))) (S_cont hM.1 hN.1)
    have hsub : Ioo (0 : ℝ) 1 ⊆ {t | u * S rho nu t + (1 - u) * S rhoAlt nuAlt t ≤
        S (mix u rho rhoAlt) (mix u nu nuAlt) t} := by
      intro t ht
      simp only [mem_ofPred_eq]
      rw [S_eq ht.1, S_eq ht.1, S_eq ht.1]
      exact Qf_concave t ht.1 ht.2 hu hrho.1 hrhoAlt.1 hnu.1 hnuAlt.1
    have := closure_minimal hsub hc
    rwa [closure_Ioo zero_ne_one] at this
  exact log_mix (S_nonneg hrho.1 hnu.1 a) (S_nonneg hrhoAlt.1 hnuAlt.1 a) hu (key ha)

end X5RM
end X5mod_RM_JC

section X5mod_RM_RE
open Matrix MeasureTheory Set Filter Topology
open scoped ComplexOrder

namespace X5RM
open X5DP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- finite value of the relative entropy -/
noncomputable def Dr (X Y : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) X - X * cfc Real.log Y).trace.re

lemma D_sum {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Dr X Y = ∑ i, ∑ j, (hX.eigenvalues j * Real.log (hX.eigenvalues j) -
      Real.log (hY.eigenvalues i) * hX.eigenvalues j) * X5OL.w hY hX i j := by
  unfold Dr
  have e1 : cfc (fun x : ℝ => x * Real.log x) X =
      cfc (fun _ : ℝ => (1 : ℝ)) Y * cfc (fun x : ℝ => x * Real.log x) X := by
    rw [cfc_const_one ℝ Y, Matrix.one_mul]
  have e2 : (X * cfc Real.log Y).trace = (cfc Real.log Y * cfc (fun x : ℝ => x) X).trace := by
    rw [cfc_id' ℝ X hX.isSelfAdjoint, Matrix.trace_mul_comm]
  rw [Matrix.trace_sub, e2, e1, X5OL.tr_cfc_cfc hY hX, X5OL.tr_cfc_cfc hY hX, Complex.sub_re,
    Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.re_sum, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma term_lim {l m w : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) (hw : l ≠ 0 → m = 0 → w = 0) :
    Tendsto (fun t => w * (((if m = 0 then 0 else Real.rpow m (1 - t)) *
      (if l = 0 then 0 else Real.rpow l t) - l) / (1 - t))) (𝓝[<] 1)
      (𝓝 (-((l * Real.log l - Real.log m * l) * w))) := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul, mul_zero, neg_zero]; exact tendsto_const_nhds
  rcases eq_or_lt_of_le hl with e | hl'
  · subst e
    simp only [if_true, mul_zero, sub_zero, zero_div, mul_zero, zero_mul, Real.log_zero,
      sub_self, neg_zero]
    exact tendsto_const_nhds
  have hm' : 0 < m := lt_of_le_of_ne hm (fun e => hw0 (hw hl'.ne' e.symm))
  set h : ℝ → ℝ := fun t => Real.exp ((1 - t) * Real.log m + t * Real.log l)
  have hd : HasDerivAt h (h 1 * (Real.log l - Real.log m)) 1 := by
    have : HasDerivAt (fun t : ℝ => (1 - t) * Real.log m + t * Real.log l)
        (Real.log l - Real.log m) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).const_sub 1).mul_const (Real.log m) |>.add
        ((hasDerivAt_id (1 : ℝ)).mul_const (Real.log l))
      exact this.congr_deriv (by ring)
    exact this.exp
  have h1 : h 1 = l := by simp [h, Real.exp_log hl']
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono _ (fun t (ht : t ∈ Iio (1 : ℝ)) => ne_of_lt ht))
  have := (hs.const_mul (-w))
  rw [h1] at this
  refine (this.congr' ?_).trans (le_of_eq (by congr 1; ring))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - 1 ≠ 0 := sub_ne_zero.2 (ne_of_lt ht)
  simp only [slope_def_field, if_neg hm'.ne', if_neg hl'.ne', h1]
  have eh : h t = Real.rpow m (1 - t) * Real.rpow l t := by
    simp only [h, Real.rpow_eq_pow, Real.rpow_def_of_pos hm', Real.rpow_def_of_pos hl', ← Real.exp_add]
    ring_nf
  rw [eh, show (1 : ℝ) - t = -(t - 1) by ring, div_neg]
  ring

lemma S_lim {X Y : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    Tendsto (fun t => (S X Y t - 1) / (1 - t)) (𝓝[<] 1) (𝓝 (-Dr X Y)) := by
  have hX1 := hX.1.1
  have hY1 := hY.1
  have hone : (1 : ℝ) = ∑ i, ∑ j, hX1.eigenvalues j * X5OL.w hY1 hX1 i j := by
    rw [Finset.sum_comm]
    have : X.trace.re = 1 := by rw [hX.2]; simp
    rw [← this, hX1.trace_eq_sum_eigenvalues, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, w_col, mul_one]; simp
  have e : (fun t => (S X Y t - 1) / (1 - t)) = fun t => ∑ i, ∑ j, X5OL.w hY1 hX1 i j *
      (((if hY1.eigenvalues i = 0 then 0 else Real.rpow (hY1.eigenvalues i) (1 - t)) *
      (if hX1.eigenvalues j = 0 then 0 else Real.rpow (hX1.eigenvalues j) t) -
        hX1.eigenvalues j) / (1 - t)) := by
    funext t
    have key : ∀ A : ℝ, A - 1 = A - ∑ i, ∑ j, hX1.eigenvalues j * X5OL.w hY1 hX1 i j :=
      fun A => by rw [← hone]
    rw [key (S X Y t), S_sum hX1 hY1]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, D_sum hX1 hY1, ← Finset.sum_neg_distrib]
  refine tendsto_finsetSum _ fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine tendsto_finsetSum _ fun j _ => ?_
  refine term_lim (hX.1.eigenvalues_nonneg j) (hY.eigenvalues_nonneg i) fun hl hm => ?_
  rw [w_swap hX1 hY1 j i]
  simp [X5OL.w, X5OL.supp_fwd hX1 hY1 hs j i hl hm]

lemma mix_supp {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {X X' Y Y' : Matrix ι ι ℂ}
    (hY : Y.PosSemidef) (hY' : Y'.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin)
    (hs' : LinearMap.ker Y'.mulVecLin ≤ LinearMap.ker X'.mulVecLin) :
    LinearMap.ker (mix u Y Y').mulVecLin ≤ LinearMap.ker (mix u X X').mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have q : star v ⬝ᵥ (mix u Y Y' *ᵥ v) = (u : ℂ) * (star v ⬝ᵥ (Y *ᵥ v)) +
      ((1 - u : ℝ) : ℂ) * (star v ⬝ᵥ (Y' *ᵥ v)) := by
    simp only [mix, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hv, dotProduct_zero] at q
  have a1 := Complex.nonneg_iff.1 (hY.dotProduct_mulVec_nonneg v)
  have a2 := Complex.nonneg_iff.1 (hY'.dotProduct_mulVec_nonneg v)
  have qr := congrArg Complex.re q
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.zero_re] at qr
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have r1 : (star v ⬝ᵥ (Y *ᵥ v)).re = 0 := by
    refine le_antisymm ?_ a1.1
    by_contra h; push_neg at h
    nlinarith [mul_pos hu.1 h, mul_nonneg hu1.le a2.1]
  have r2 : (star v ⬝ᵥ (Y' *ᵥ v)).re = 0 := by
    refine le_antisymm ?_ a2.1
    by_contra h; push_neg at h
    nlinarith [mul_pos hu1 h, mul_nonneg hu.1.le a1.1]
  have b1 : Y *ᵥ v = 0 := (hY.dotProduct_mulVec_zero_iff v).1 (Complex.ext r1 a1.2.symm)
  have b2 : Y' *ᵥ v = 0 := (hY'.dotProduct_mulVec_zero_iff v).1 (Complex.ext r2 a2.2.symm)
  have c1 : X *ᵥ v = 0 := by
    have := hs (show v ∈ LinearMap.ker Y.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact b1)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have c2 : X' *ᵥ v = 0 := by
    have := hs' (show v ∈ LinearMap.ker Y'.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact b2)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  simp only [mix, add_mulVec, smul_mulVec, c1, c2, smul_zero, add_zero]

end X5RM
end X5mod_RM_RE

section X5mod_RM_RJ
open Matrix MeasureTheory Set Filter Topology
open scoped ComplexOrder

namespace X5RM
open X5DP
open QAlgorithms.Papers.Independent.Next46.P23

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma sRE_pos {X Y : Matrix ι ι ℂ} (h : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    signedRelativeEntropy X Y = ((-Dr X Y : ℝ) : EReal) := by
  unfold signedRelativeEntropy QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported
  rw [if_pos h, EReal.coe_neg]; rfl

lemma sRE_neg {X Y : Matrix ι ι ℂ} (h : ¬ LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    signedRelativeEntropy X Y = ⊥ := by
  unfold signedRelativeEntropy QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported
  rw [if_neg h]; rfl

lemma mix_dens {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {X X' : Matrix ι ι ℂ}
    (hX : QAlgorithms.IsDensityMatrix X) (hX' : QAlgorithms.IsDensityMatrix X') :
    QAlgorithms.IsDensityMatrix (mix u X X') := by
  refine ⟨mix_psd hu hX.1 hX'.1, ?_⟩
  simp only [mix, Matrix.trace_add, Matrix.trace_smul, hX.2, hX'.2, smul_eq_mul, mul_one]
  push_cast; ring

theorem rjoint (rho rhoAlt nu nuAlt : Matrix ι ι ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hrhoAlt : QAlgorithms.IsDensityMatrix rhoAlt)
    (hnu : QAlgorithms.IsDensityMatrix nu) (hnuAlt : QAlgorithms.IsDensityMatrix nuAlt)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (u : EReal) * signedRelativeEntropy rho nu + ((1-u : ℝ) : EReal) * signedRelativeEntropy rhoAlt nuAlt ≤
      signedRelativeEntropy ((u : ℂ) • rho + ((1-u : ℝ) : ℂ) • rhoAlt)
        ((u : ℂ) • nu + ((1-u : ℝ) : ℂ) • nuAlt) := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · subst h0
    simp
  rcases eq_or_lt_of_le hu.2 with h1 | h1
  · subst h1
    simp
  have hv : 0 < 1 - u := by linarith
  by_cases s1 : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin
  swap
  · rw [sRE_neg s1, EReal.coe_mul_bot_of_pos h0, EReal.bot_add]; exact bot_le
  by_cases s2 : LinearMap.ker nuAlt.mulVecLin ≤ LinearMap.ker rhoAlt.mulVecLin
  swap
  · rw [sRE_neg s2, EReal.coe_mul_bot_of_pos hv, EReal.add_bot]; exact bot_le
  have sm := mix_supp ⟨h0, h1⟩ hnu.1 hnuAlt.1 s1 s2
  change _ ≤ signedRelativeEntropy (mix u rho rhoAlt) (mix u nu nuAlt)
  rw [sRE_pos s1, sRE_pos s2, sRE_pos sm, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  have L1 := S_lim hrho hnu.1 s1
  have L2 := S_lim hrhoAlt hnuAlt.1 s2
  have L3 := S_lim (mix_dens hu hrho hrhoAlt) (mix_psd hu hnu.1 hnuAlt.1) sm
  refine le_of_tendsto_of_tendsto ((L1.const_mul u).add (L2.const_mul (1 - u))) L3 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hc := Qf_concave t ht.1 ht.2 hu hrho.1 hrhoAlt.1 hnu.1 hnuAlt.1
  rw [← S_eq ht.1, ← S_eq ht.1, ← S_eq ht.1] at hc
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have e : ∀ a b : ℝ, u * (a / (1 - t)) + (1 - u) * (b / (1 - t)) = (u * a + (1 - u) * b) / (1 - t) :=
    fun a b => by field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) ht1.le

end X5RM
end X5mod_RM_RJ

section X5mod_RM_EC
open Matrix MeasureTheory Set Filter Topology
open scoped ComplexOrder

namespace X5RM
open X5DP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma sum_eig {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : ∑ i, hX.eigenvalues i = X.trace.re := by
  rw [hX.trace_eq_sum_eigenvalues, Complex.re_sum]; simp

lemma S_le_one {X Y : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X)
    (hY : QAlgorithms.IsDensityMatrix Y) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : S X Y t ≤ 1 := by
  have hX1 := hX.1.1
  have hY1 := hY.1.1
  rw [S_sum hX1 hY1]
  have hb : ∀ i j, (if hY1.eigenvalues i = 0 then 0 else Real.rpow (hY1.eigenvalues i) (1 - t)) *
      (if hX1.eigenvalues j = 0 then 0 else Real.rpow (hX1.eigenvalues j) t) ≤
      (1 - t) * hY1.eigenvalues i + t * hX1.eigenvalues j := by
    intro i j
    have a := hY.1.eigenvalues_nonneg i
    have b := hX.1.eigenvalues_nonneg j
    by_cases e1 : hY1.eigenvalues i = 0
    · simp only [e1, if_true, zero_mul]; nlinarith
    by_cases e2 : hX1.eigenvalues j = 0
    · simp only [e2, if_true, mul_zero]; nlinarith
    simp only [e1, e2, if_false, Real.rpow_eq_pow]
    exact Real.geom_mean_le_arith_mean2_weighted (by linarith) h0.le a b (by ring)
  calc _ ≤ ∑ i, ∑ j, ((1 - t) * hY1.eigenvalues i + t * hX1.eigenvalues j) * X5OL.w hY1 hX1 i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hb i j) (X5OL.w_nonneg _ _ _ _)
    _ = (1 - t) * ∑ i, hY1.eigenvalues i * (∑ j, X5OL.w hY1 hX1 i j) +
          t * ∑ j, hX1.eigenvalues j * (∑ i, X5OL.w hY1 hX1 i j) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    _ = 1 := by
        simp only [X5OL.w_row, w_col, mul_one, sum_eig]
        rw [hX.2, hY.2]; simp

theorem klein {X Y : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X)
    (hY : QAlgorithms.IsDensityMatrix Y)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) : 0 ≤ Dr X Y := by
  have L := S_lim hX hY.1 hs
  have : -Dr X Y ≤ 0 := by
    refine le_of_tendsto L ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [S_le_one hX hY ht.1 ht.2]) (by linarith [ht.2])
  linarith

lemma w_self {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (i j : ι) :
    X5OL.w hX hX i j = if i = j then 1 else 0 := by
  have : X5OL.ov hX hX = 1 := Unitary.star_mul_self_of_mem (hX.eigenvectorUnitary).2
  unfold X5OL.w
  rw [this, one_apply]
  split_ifs <;> simp

lemma Dr_self {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : Dr X X = 0 := by
  rw [D_sum hX hX]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [w_self]
  by_cases h : i = j
  · subst h; simp only [if_true]; ring
  · simp [h]

lemma tr_cfc {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace.re = ∑ i, f (hX.eigenvalues i) := by
  have : cfc f X = cfc f X * cfc (fun _ : ℝ => (1 : ℝ)) X := by rw [cfc_const_one ℝ X, Matrix.mul_one]
  rw [this, X5OL.tr_cfc_cfc hX hX, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.re_sum, Complex.ofReal_re, w_self, mul_one]
  simp

lemma Dr_split (X Y : Matrix ι ι ℂ) :
    Dr X Y = (cfc (fun x : ℝ => x * Real.log x) X).trace.re - (X * cfc Real.log Y).trace.re := by
  unfold Dr; rw [Matrix.trace_sub, Complex.sub_re]

lemma tr_mix_mul (u : ℝ) (X X' M : Matrix ι ι ℂ) :
    (mix u X X' * M).trace.re = u * (X * M).trace.re + (1 - u) * (X' * M).trace.re := by
  simp [mix, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]

lemma ker_mix {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {Y Y' : Matrix ι ι ℂ}
    (hY : Y.PosSemidef) (hY' : Y'.PosSemidef) :
    LinearMap.ker (mix u Y Y').mulVecLin ≤ LinearMap.ker Y.mulVecLin ∧
      LinearMap.ker (mix u Y Y').mulVecLin ≤ LinearMap.ker Y'.mulVecLin := by
  have a := mix_supp (X := Y) (X' := 0) hu hY hY' le_rfl (by
    intro v _; simp)
  have b := mix_supp (X := 0) (X' := Y') hu hY hY' (by intro v _; simp) le_rfl
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
  have hu1 : ((1 - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show 1 - u ≠ 0 by linarith [hu.2])
  constructor
  · intro v hv
    have := a hv
    simp only [LinearMap.mem_ker, mulVecLin_apply, mix, add_mulVec, smul_mulVec, zero_mulVec,
      smul_zero, add_zero] at this ⊢
    exact (smul_eq_zero.1 this).resolve_left hu0
  · intro v hv
    have := b hv
    simp only [LinearMap.mem_ker, mulVecLin_apply, mix, add_mulVec, smul_mulVec, zero_mulVec,
      smul_zero, zero_add] at this ⊢
    exact (smul_eq_zero.1 this).resolve_left hu1

theorem ent_concave {X X' : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X)
    (hX' : QAlgorithms.IsDensityMatrix X') (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u * entropy X + (1 - u) * entropy X' ≤ entropy ((u : ℂ) • X + ((1 - u : ℝ) : ℂ) • X') := by
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · subst h0; simp
  rcases eq_or_lt_of_le hu1 with h1 | h1
  · subst h1; simp
  change _ ≤ entropy (mix u X X')
  have hm := mix_dens ⟨hu0, hu1⟩ hX hX'
  obtain ⟨s1, s2⟩ := ker_mix ⟨h0, h1⟩ hX.1 hX'.1
  have k1 := klein hX hm s1
  have k2 := klein hX' hm s2
  have k3 := Dr_self hm.1.1
  rw [Dr_split] at k1 k2 k3
  rw [tr_mix_mul] at k3
  unfold entropy
  nlinarith [mul_nonneg hu0 k1, mul_nonneg (show 0 ≤ 1 - u by linarith) k2]

section gibbs
variable [Nonempty ι]

/-- partition function via the real functional calculus -/
noncomputable def Zf (A : Matrix ι ι ℂ) : ℝ := (cfc Real.exp A).trace.re

lemma Zf_pos {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : 0 < Zf A := by
  unfold Zf; rw [tr_cfc hA]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- the Gibbs state -/
noncomputable def σf (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc (fun x => Real.exp x / Zf A) A

lemma cfc_psd {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (cfc f A).PosSemidef := by
  rw [hA.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  rw [star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same ?_ _
  refine (posSemidef_diagonal_iff).2 fun i => ?_
  simp only [Function.comp_apply]
  exact Complex.zero_le_real.2 (hf _)

lemma σ_dens {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : QAlgorithms.IsDensityMatrix (σf A) := by
  refine ⟨cfc_psd hA _ fun x => div_nonneg (Real.exp_pos x).le (Zf_pos hA).le, ?_⟩
  have h1 : (σf A).trace.re = 1 := by
    unfold σf
    rw [tr_cfc hA, ← Finset.sum_div]
    have : Zf A = ∑ i, Real.exp (hA.eigenvalues i) := by unfold Zf; rw [tr_cfc hA]
    rw [← this]; exact div_self (Zf_pos hA).ne'
  have h2 : (σf A).trace.im = 0 := by
    have := (cfc_psd hA (fun x => Real.exp x / Zf A)
      fun x => div_nonneg (Real.exp_pos x).le (Zf_pos hA).le).trace_nonneg
    exact (Complex.nonneg_iff.1 this).2.symm
  exact Complex.ext h1 h2

lemma σ_ker {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (X : Matrix ι ι ℂ) :
    LinearMap.ker (σf A).mulVecLin ≤ LinearMap.ker X.mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv
  have e : cfc (fun x => Zf A * Real.exp (-x)) A * σf A = 1 := by
    unfold σf
    rw [← cfc_mul (fun x => Zf A * Real.exp (-x)) (fun x => Real.exp x / Zf A) A]
    rw [← cfc_const_one ℝ A]
    refine cfc_congr fun x _ => ?_
    have := (Zf_pos hA).ne'
    field_simp
    rw [← Real.exp_add]; simp
  have : v = 0 := by
    rw [← one_mulVec v, ← e, ← mulVec_mulVec, hv, mulVec_zero]
  rw [this]; exact Submodule.zero_mem _

lemma log_σ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    cfc Real.log (σf A) = A - Real.log (Zf A) • (1 : Matrix ι ι ℂ) := by
  have hZ := (Zf_pos hA).ne'
  unfold σf
  rw [← cfc_comp' Real.log (fun x => Real.exp x / Zf A) A
    (Real.continuousOn_log.mono (by rintro _ ⟨x, _, rfl⟩; simp [hZ]))]
  have : (fun x => Real.log (Real.exp x / Zf A)) = fun x => x - Real.log (Zf A) := by
    funext x; rw [Real.log_div (Real.exp_pos x).ne' hZ, Real.log_exp]
  rw [this, cfc_sub (fun x => x) (fun _ => Real.log (Zf A)) A, cfc_id' ℝ A, cfc_const _ A,
    Algebra.algebraMap_eq_smul_one]

lemma tr_log_σ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {X : Matrix ι ι ℂ}
    (hX : QAlgorithms.IsDensityMatrix X) :
    (X * cfc Real.log (σf A)).trace.re = (X * A).trace.re - Real.log (Zf A) := by
  rw [log_σ hA, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Complex.sub_re,
    Matrix.trace_smul, hX.2]
  simp

theorem gibbs_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {X : Matrix ι ι ℂ}
    (hX : QAlgorithms.IsDensityMatrix X) : (X * A).trace.re + entropy X ≤ Real.log (Zf A) := by
  have k := klein hX (σ_dens hA) (σ_ker hA X)
  rw [Dr_split, tr_log_σ hA hX] at k
  unfold entropy; linarith

theorem gibbs_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (σf A * A).trace.re + entropy (σf A) = Real.log (Zf A) := by
  have k := Dr_self (σ_dens hA).1.1
  rw [Dr_split, tr_log_σ hA (σ_dens hA)] at k
  unfold entropy; linarith

theorem logZ_convex {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.log (Zf ((u : ℂ) • A + ((1 - u : ℝ) : ℂ) • B)) ≤
      u * Real.log (Zf A) + (1 - u) * Real.log (Zf B) := by
  have hC : ((u : ℂ) • A + ((1 - u : ℝ) : ℂ) • B).IsHermitian := by
    refine IsHermitian.add ?_ ?_
    · unfold IsHermitian; rw [conjTranspose_smul, hA.eq]; simp
    · unfold IsHermitian; rw [conjTranspose_smul, hB.eq]; simp
  have e := gibbs_eq hC
  have g1 := gibbs_le hA (σ_dens hC)
  have g2 := gibbs_le hB (σ_dens hC)
  have t : (σf ((u : ℂ) • A + ((1 - u : ℝ) : ℂ) • B) * ((u : ℂ) • A + ((1 - u : ℝ) : ℂ) • B)).trace.re =
      u * (σf ((u : ℂ) • A + ((1 - u : ℝ) : ℂ) • B) * A).trace.re +
        (1 - u) * (σf ((u : ℂ) • A + ((1 - u : ℝ) : ℂ) • B) * B).trace.re := by
    simp [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  rw [t] at e
  nlinarith [mul_le_mul_of_nonneg_left g1 hu0, mul_le_mul_of_nonneg_left g2 (show 0 ≤ 1 - u by linarith)]

end gibbs

end X5RM
end X5mod_RM_EC

section X5mod_SK_Strict
open Matrix Set Filter Topology
open scoped ComplexOrder

namespace X5SK
open X5DP X5RM

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- scalar Klein term -/
lemma g_nonneg {l m : ℝ} (hl : 0 ≤ l) (hm : 0 < m) :
    0 ≤ l * Real.log l - Real.log m * l - l + m ∧
      (l * Real.log l - Real.log m * l - l + m = 0 → l = m) := by
  rcases eq_or_lt_of_le hl with h0 | h0
  · subst h0; simp only [zero_mul, mul_zero, sub_zero, zero_add]
    exact ⟨hm.le, fun h => (hm.ne' h).elim⟩
  have e : l * Real.log l - Real.log m * l - l + m = -(l * Real.log (m / l)) + m - l := by
    rw [Real.log_div hm.ne' h0.ne']; ring
  have hq : 0 < m / l := div_pos hm h0
  rw [e]
  constructor
  · have := Real.log_le_sub_one_of_pos hq
    have := mul_le_mul_of_nonneg_left this h0.le
    rw [mul_sub, mul_div_cancel₀ _ h0.ne', mul_one] at this
    linarith
  · intro hz
    by_contra hne
    have hq1 : m / l ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have := Real.log_lt_sub_one_of_pos hq hq1
    have := mul_lt_mul_of_pos_left this h0
    rw [mul_sub, mul_div_cancel₀ _ h0.ne', mul_one] at this
    linarith

lemma term {l m w : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) (hw0 : 0 ≤ w) (hw : l ≠ 0 → m = 0 → w = 0) :
    0 ≤ (l * Real.log l - Real.log m * l - l + m) * w ∧
      ((l * Real.log l - Real.log m * l - l + m) * w = 0 → w ≠ 0 → l = m) := by
  rcases eq_or_lt_of_le hm with h0 | h0
  · subst h0
    by_cases hl0 : l = 0
    · subst hl0; simp
    · rw [hw hl0 rfl]; simp
  obtain ⟨a, b⟩ := g_nonneg hl h0
  refine ⟨mul_nonneg a hw0, fun hz hne => b ?_⟩
  rcases mul_eq_zero.1 hz with h | h
  · exact h
  · exact (hne h).elim

/-- strict Klein inequality: zero relative entropy forces equality -/
theorem klein_eq {X Y : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X)
    (hY : QAlgorithms.IsDensityMatrix Y)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) (h : Dr X Y = 0) : X = Y := by
  have hX1 := hX.1.1
  have hY1 := hY.1.1
  set l := hX1.eigenvalues
  set m := hY1.eigenvalues
  set W := X5OL.w hY1 hX1
  have hsum : ∑ i, ∑ j, (m i - l j) * W i j = 0 := by
    have a : ∑ i, ∑ j, m i * W i j = 1 := by
      simp only [← Finset.mul_sum, W, X5OL.w_row, mul_one, m, sum_eig]
      rw [hY.2]; simp
    have b : ∑ i, ∑ j, l j * W i j = 1 := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, W, w_col, mul_one, l, sum_eig]
      rw [hX.2]; simp
    simp only [sub_mul, Finset.sum_sub_distrib, a, b, sub_self]
  have hD := D_sum hX1 hY1
  have hT : ∀ i j, l j ≠ 0 → m i = 0 → W i j = 0 := by
    intro i j hl hm
    show X5OL.w hY1 hX1 i j = 0
    rw [w_swap hX1 hY1 j i]
    simp [X5OL.w, X5OL.supp_fwd hX1 hY1 hs j i hl hm]
  have tm := fun i j => term (hX.1.eigenvalues_nonneg j) (hY.1.eigenvalues_nonneg i)
    (X5OL.w_nonneg hY1 hX1 i j) (hT i j)
  have htot : ∑ i, ∑ j, (l j * Real.log (l j) - Real.log (m i) * l j - l j + m i) * W i j = 0 := by
    have : ∑ i, ∑ j, (l j * Real.log (l j) - Real.log (m i) * l j - l j + m i) * W i j =
        Dr X Y + ∑ i, ∑ j, (m i - l j) * W i j := by
      rw [hD, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, h, hsum, add_zero]
  have heq : ∀ i j, W i j ≠ 0 → l j = m i := by
    intro i j hw
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => (tm i j).1).1 htot i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => (tm i j).1).1 h1 j (Finset.mem_univ _)
    exact (tm i j).2 h2 hw
  -- matrix part
  set U := (hY1.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hX1.eigenvectorUnitary : Matrix ι ι ℂ)
  set O := X5OL.ov hY1 hX1
  set DL := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ l)
  set DM := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ m)
  have hO : O * DL = DM * O := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases h0 : O i j = 0
    · simp [h0]
    · have : W i j ≠ 0 := by
        simp only [W, X5OL.w]; exact pow_ne_zero _ (norm_ne_zero_iff.2 h0)
      simp only [Function.comp_apply, heq i j this]; ring
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem (hY1.eigenvectorUnitary).2
  have hV : V = U * O := by
    simp only [O, X5OL.ov, U, V]; rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have eX : X = V * DL * star V := by
    conv_lhs => rw [hX1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have eY : Y = U * DM * star U := by
    conv_lhs => rw [hY1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  rw [eX, eY, hV, star_mul]
  have hOO : O * star O = 1 := X5OL.ov_unitary hY1 hX1
  calc U * O * DL * (star O * star U) = U * (O * DL) * star O * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * DM * (O * star O) * star U := by rw [hO]; simp only [Matrix.mul_assoc]
    _ = U * DM * star U := by rw [hOO, Matrix.mul_one]

end X5SK
end X5mod_SK_Strict

section X5mod_EP_Cfc
open Matrix Polynomial

namespace X5EP

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma aeval_diag (d : I → ℝ) (p : ℝ[X]) :
    aeval (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) p = diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, diagonal_add]; congr 1; funext i; simp
  | monomial n a =>
    rw [aeval_monomial, diagonal_pow, Matrix.algebraMap_eq_diagonal, diagonal_mul_diagonal]
    congr 1; funext i; simp [eval_monomial]

lemma cfc_diag (d : I → ℝ) (g : ℝ → ℝ) :
    cfc g (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) = diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ d) := by
  set D := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)
  have hD : IsSelfAdjoint D := by
    unfold D IsSelfAdjoint; rw [star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hf : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := hf.toFinset ∪ Finset.univ.image d
  set p := Lagrange.interpolate s (fun x : ℝ => x) g
  have hp : ∀ x ∈ s, p.eval x = g x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) g (fun a _ b _ h => h) hx
  have : cfc g D = aeval D p := by
    rw [← cfc_polynomial p D hD]
    exact cfc_congr fun x hx => (hp x (Finset.mem_union_left _ (hf.mem_toFinset.2 hx))).symm
  rw [this, aeval_diag]
  congr 1; funext i
  simp only [Function.comp_apply]
  rw [hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))]
  rfl

/-- conjugation by a unitary as a star algebra hom -/
noncomputable def cj (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) : Matrix I I ℂ →⋆ₐ[ℂ] Matrix I I ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) ⟨U, hU⟩ : _ ≃⋆ₐ[ℂ] _).toStarAlgHom

lemma cj_apply (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) (X : Matrix I I ℂ) :
    cj U hU X = U * X * star U := rfl

lemma sa_cj {U : Matrix I I ℂ} (hU : U ∈ unitaryGroup I ℂ) {X : Matrix I I ℂ} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (U * X * star U) := by
  unfold IsSelfAdjoint; rw [star_mul, star_mul, star_star, hX.star_eq, Matrix.mul_assoc]

lemma cfc_conj {U : Matrix I I ℂ} (hU : U ∈ unitaryGroup I ℂ) {X : Matrix I I ℂ} (hX : IsSelfAdjoint X)
    (f : ℝ → ℝ) : cfc f (U * X * star U) = U * cfc f X * star U := by
  have hc : Continuous (cj U hU) := by
    change Continuous fun X : Matrix I I ℂ => U * X * star U
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (cj U hU) f X (X.finite_real_spectrum.continuousOn _) hc hX (sa_cj hU hX)
  exact h.symm

lemma cfc_UD {U : Matrix I I ℂ} (hU : U ∈ unitaryGroup I ℂ) (d : I → ℝ) (g : ℝ → ℝ) :
    cfc g (U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d) * star U) =
      U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ d) * star U := by
  have hD : IsSelfAdjoint (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) := by
    unfold IsSelfAdjoint; rw [star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_conj hU hD, cfc_diag]

section kron
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma spec {X : Matrix I I ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix I I ℂ) *
      diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hX.eigenvalues) *
        star (hX.eigenvectorUnitary : Matrix I I ℂ) := by
  rw [hX.cfc_eq]; unfold IsHermitian.cfc; rw [Unitary.conjStarAlgAut_apply]

lemma kron_unitary {U : Matrix I I ℂ} {V : Matrix J J ℂ} (hU : U ∈ unitaryGroup I ℂ)
    (hV : V ∈ unitaryGroup J ℂ) : kroneckerMap (· * ·) U V ∈ unitaryGroup (I × J) ℂ := by
  rw [mem_unitaryGroup_iff] at *
  rw [star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul, ← star_eq_conjTranspose,
    ← star_eq_conjTranspose, hU, hV, one_kronecker_one]

/-- functional calculus of a Kronecker product -/
lemma cfc_kron {X : Matrix I I ℂ} {Y : Matrix J J ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (g : ℝ → ℝ) : cfc g (kroneckerMap (· * ·) X Y) =
      kroneckerMap (· * ·) (hX.eigenvectorUnitary : Matrix I I ℂ) (hY.eigenvectorUnitary : Matrix J J ℂ) *
        diagonal (fun ij : I × J => ((g (hX.eigenvalues ij.1 * hY.eigenvalues ij.2) : ℝ) : ℂ)) *
          star (kroneckerMap (· * ·) (hX.eigenvectorUnitary : Matrix I I ℂ)
            (hY.eigenvectorUnitary : Matrix J J ℂ)) := by
  set U := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hY.eigenvectorUnitary : Matrix J J ℂ)
  have eX : X = U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hX.eigenvalues) * star U := by
    conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
    rw [spec hX]; rfl
  have eY : Y = V * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hY.eigenvalues) * star V := by
    conv_lhs => rw [← cfc_id' ℝ Y hY.isSelfAdjoint]
    rw [spec hY]; rfl
  have hW := kron_unitary (hX.eigenvectorUnitary).2 (hY.eigenvectorUnitary).2
  have e : kroneckerMap (· * ·) X Y = kroneckerMap (· * ·) U V *
      diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ fun ij : I × J => hX.eigenvalues ij.1 * hY.eigenvalues ij.2) *
        star (kroneckerMap (· * ·) U V) := by
    conv_lhs => rw [eX, eY]
    rw [mul_kronecker_mul, mul_kronecker_mul, diagonal_kronecker_diagonal, star_eq_conjTranspose,
      star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_kronecker]
    congr 3; funext ij; simp
  rw [e, cfc_UD hW]
  rfl

end kron

end X5EP
end X5mod_EP_Cfc

section X5mod_EP_PT
open Matrix
open scoped ComplexOrder Kronecker

namespace X5EP
set_option linter.unusedSectionVars false
open QAlgorithms

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def emb (a : A) (y : B → ℂ) : A × B → ℂ := fun p => if p.1 = a then y p.2 else 0
def emb' (b : B) (x : A → ℂ) : A × B → ℂ := fun p => if p.2 = b then x p.1 else 0

lemma pt_kron (rho : Matrix (A × B) (A × B) ℂ) (Y : Matrix B B ℂ) :
    (rho * ((1 : Matrix A A ℂ) ⊗ₖ Y)).trace = (traceLeft rho * Y).trace := by
  simp only [Matrix.trace, diag_apply, mul_apply, kronecker_apply, one_apply, traceLeft, of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma pt_kron' (rho : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    (rho * (X ⊗ₖ (1 : Matrix B B ℂ))).trace = (traceRight rho * X).trace := by
  simp only [Matrix.trace, diag_apply, mul_apply, kronecker_apply, one_apply, traceRight, of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
    mul_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma qf_emb (rho : Matrix (A × B) (A × B) ℂ) (y : B → ℂ) :
    star y ⬝ᵥ (traceLeft rho *ᵥ y) = ∑ a, star (emb a y) ⬝ᵥ (rho *ᵥ emb a y) := by
  simp only [dotProduct, mulVec, traceLeft, of_apply, emb, Pi.star_apply, Fintype.sum_prod_type,
    apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ x : B, ∑ i : A, ∑ y1 : B, star (y x) * (rho (i, x) (i, y1) * y y1) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma qf_emb' (rho : Matrix (A × B) (A × B) ℂ) (x : A → ℂ) :
    star x ⬝ᵥ (traceRight rho *ᵥ x) = ∑ b, star (emb' b x) ⬝ᵥ (rho *ᵥ emb' b x) := by
  simp only [dotProduct, mulVec, traceRight, of_apply, emb', Pi.star_apply, Fintype.sum_prod_type,
    apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma tl_psd {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) : (traceLeft rho).PosSemidef := by
  have hH : (traceLeft rho).IsHermitian := by
    ext b b'
    simp only [conjTranspose_apply, traceLeft, of_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := congrFun (congrFun h.isHermitian (a, b)) (a, b')
    rw [conjTranspose_apply] at this
    exact this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  rw [qf_emb]
  exact Finset.sum_nonneg fun a _ => h.dotProduct_mulVec_nonneg _

lemma tr_psd {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) : (traceRight rho).PosSemidef := by
  have hH : (traceRight rho).IsHermitian := by
    ext a a'
    simp only [conjTranspose_apply, traceRight, of_apply, star_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := congrFun (congrFun h.isHermitian (a, b)) (a', b)
    rw [conjTranspose_apply] at this
    exact this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  rw [qf_emb']
  exact Finset.sum_nonneg fun b _ => h.dotProduct_mulVec_nonneg _

lemma tl_trace (rho : Matrix (A × B) (A × B) ℂ) : (traceLeft rho).trace = rho.trace := by
  simp only [Matrix.trace, diag_apply, traceLeft, of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma tr_trace (rho : Matrix (A × B) (A × B) ℂ) : (traceRight rho).trace = rho.trace := by
  simp only [Matrix.trace, diag_apply, traceRight, of_apply, Fintype.sum_prod_type]

lemma tl_density {rho : Matrix (A × B) (A × B) ℂ} (h : IsDensityMatrix rho) :
    IsDensityMatrix (traceLeft rho) := ⟨tl_psd h.1, by rw [tl_trace, h.2]⟩

lemma tr_density {rho : Matrix (A × B) (A × B) ℂ} (h : IsDensityMatrix rho) :
    IsDensityMatrix (traceRight rho) := ⟨tr_psd h.1, by rw [tr_trace, h.2]⟩

end X5EP
end X5mod_EP_PT

section X5mod_EP_Sub
open Matrix
open scoped ComplexOrder Kronecker

namespace X5EP
set_option linter.unusedSectionVars false
open QAlgorithms X5RM
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

noncomputable def ind : ℝ → ℝ := fun x => if x = 0 then 0 else 1
noncomputable def pinv : ℝ → ℝ := fun x => if x = 0 then 0 else x⁻¹

section
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cm (X : Matrix I I ℂ) (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (fin _ _) (fin _ _)).symm

lemma XP {X : Matrix I I ℂ} (hX : X.IsHermitian) : X * cfc ind X = X := by
  have : X * cfc ind X = cfc (fun x : ℝ => x) X * cfc ind X := by rw [cfc_id' ℝ X hX.isSelfAdjoint]
  rw [this, cm]; conv_rhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  refine cfc_congr fun x _ => ?_; simp only [ind]; split_ifs with h <;> simp [h]

lemma pinvX {X : Matrix I I ℂ} (hX : X.IsHermitian) : cfc pinv X * X = cfc ind X := by
  have : cfc pinv X * X = cfc pinv X * cfc (fun x : ℝ => x) X := by rw [cfc_id' ℝ X hX.isSelfAdjoint]
  rw [this, cm]; refine cfc_congr fun x _ => ?_; simp only [ind, pinv]; split_ifs with h
  · simp
  · field_simp

lemma PP (X : Matrix I I ℂ) : cfc ind X * cfc ind X = cfc ind X := by
  rw [cm]; refine cfc_congr fun x _ => ?_; simp only [ind]; split_ifs <;> simp

lemma PH (X : Matrix I I ℂ) : (cfc ind X)ᴴ = cfc ind X :=
  (cfc_predicate ind X : IsSelfAdjoint _)

lemma xlogx {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) X = X * cfc Real.log X := by
  have : X * cfc Real.log X = cfc (fun x : ℝ => x) X * cfc Real.log X := by
    rw [cfc_id' ℝ X hX.isSelfAdjoint]
  rw [this, cm]

/-- a PSD matrix annihilated in trace by a projection is annihilated by it -/
lemma proj_zero {R Pm : Matrix I I ℂ} (hR : R.PosSemidef) (h1 : Pmᴴ = Pm) (h2 : Pm * Pm = Pm)
    (h : (R * Pm).trace = 0) : R * Pm = 0 := by
  obtain ⟨B, rfl⟩ := X5DP.exists_sq hR
  have : (B * Pm)ᴴ * (B * Pm) = Pm * (Bᴴ * B * Pm) := by
    rw [conjTranspose_mul, h1]; simp only [Matrix.mul_assoc]
  have h0 : ((B * Pm)ᴴ * (B * Pm)).trace = 0 := by
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h2]; exact h
  rw [trace_conjTranspose_mul_self_eq_zero_iff] at h0
  rw [Matrix.mul_assoc, h0, Matrix.mul_zero]

end

variable {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

lemma kronecker_sub (A : Matrix K K ℂ) (B1 B2 : Matrix L L ℂ) :
    A ⊗ₖ (B1 - B2) = A ⊗ₖ B1 - A ⊗ₖ B2 := by ext; simp [mul_sub]

lemma sub_kronecker (A1 A2 : Matrix K K ℂ) (B : Matrix L L ℂ) :
    (A1 - A2) ⊗ₖ B = A1 ⊗ₖ B - A2 ⊗ₖ B := by ext; simp [sub_mul]

lemma kron_split {X : Matrix K K ℂ} {Y : Matrix L L ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (g g1 h1 g2 h2 : ℝ → ℝ) (hg : ∀ x y, g (x * y) = g1 x * h1 y + g2 x * h2 y) :
    cfc g (X ⊗ₖ Y) = cfc g1 X ⊗ₖ cfc h1 Y + cfc g2 X ⊗ₖ cfc h2 Y := by
  change cfc g (kroneckerMap (· * ·) X Y) = _
  rw [cfc_kron hX hY, spec hX, spec hY, spec hX, spec hY]
  simp only [kronecker, mul_kronecker_mul, diagonal_kronecker_diagonal, star_eq_conjTranspose,
    conjTranspose_kronecker, ← Matrix.mul_add, ← Matrix.add_mul, diagonal_add]
  congr 3; funext ij; simp [hg]

lemma log_kron {X : Matrix K K ℂ} {Y : Matrix L L ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    cfc Real.log (X ⊗ₖ Y) = cfc Real.log X ⊗ₖ cfc ind Y + cfc ind X ⊗ₖ cfc Real.log Y := by
  refine kron_split hX hY _ _ _ _ _ fun x y => ?_
  simp only [ind]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  simp [hx, hy, Real.log_mul hx hy]

section
variable {rho : Matrix (K × L) (K × L) ℂ} (hr : IsDensityMatrix rho)
include hr

lemma kill_B : rho * ((1 : Matrix K K ℂ) ⊗ₖ (1 - cfc ind (traceLeft rho))) = 0 := by
  have hB := (tl_density hr).1.1
  refine proj_zero hr.1 ?_ ?_ ?_
  · rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_sub, conjTranspose_one, PH]
  · rw [← mul_kronecker_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, PP, sub_self, sub_zero]
  · rw [pt_kron, Matrix.mul_sub, Matrix.mul_one, XP hB, sub_self, Matrix.trace_zero]

lemma kill_A : rho * ((1 - cfc ind (traceRight rho)) ⊗ₖ (1 : Matrix L L ℂ)) = 0 := by
  have hA := (tr_density hr).1.1
  refine proj_zero hr.1 ?_ ?_ ?_
  · rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_sub, conjTranspose_one, PH]
  · rw [← mul_kronecker_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, PP, sub_self, sub_zero]
  · rw [pt_kron', Matrix.mul_sub, Matrix.mul_one, XP hA, sub_self, Matrix.trace_zero]

lemma tr_logσ : (rho * cfc Real.log (traceRight rho ⊗ₖ traceLeft rho)).trace =
    (traceRight rho * cfc Real.log (traceRight rho)).trace +
      (traceLeft rho * cfc Real.log (traceLeft rho)).trace := by
  have hA := (tr_density hr).1.1
  have hB := (tl_density hr).1.1
  set PA := cfc ind (traceRight rho)
  set PB := cfc ind (traceLeft rho)
  set LA := cfc Real.log (traceRight rho)
  set LB := cfc Real.log (traceLeft rho)
  rw [log_kron hA hB]
  have e1 : LA ⊗ₖ PB = LA ⊗ₖ (1 : Matrix L L ℂ) -
      ((1 : Matrix K K ℂ) ⊗ₖ (1 - PB)) * (LA ⊗ₖ (1 : Matrix L L ℂ)) := by
    rw [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, kronecker_sub, sub_sub_cancel]
  have e2 : PA ⊗ₖ LB = (1 : Matrix K K ℂ) ⊗ₖ LB -
      ((1 - PA) ⊗ₖ (1 : Matrix L L ℂ)) * ((1 : Matrix K K ℂ) ⊗ₖ LB) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, sub_kronecker, sub_sub_cancel]
  rw [Matrix.mul_add, e1, e2, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, kill_B hr,
    ← Matrix.mul_assoc, kill_A hr, Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero,
    Matrix.trace_add, pt_kron', pt_kron]

lemma σ_dens : IsDensityMatrix (traceRight rho ⊗ₖ traceLeft rho) :=
  ⟨(tr_density hr).1.kronecker (tl_density hr).1, by
    rw [trace_kronecker, (tr_density hr).2, (tl_density hr).2, one_mul]⟩

lemma σ_ker : LinearMap.ker (traceRight rho ⊗ₖ traceLeft rho).mulVecLin ≤
    LinearMap.ker rho.mulVecLin := by
  have hA := (tr_density hr).1.1
  have hB := (tl_density hr).1.1
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  set PA := cfc ind (traceRight rho)
  set PB := cfc ind (traceLeft rho)
  have h1 : (PA ⊗ₖ PB) *ᵥ v = 0 := by
    have : PA ⊗ₖ PB = (cfc pinv (traceRight rho) ⊗ₖ cfc pinv (traceLeft rho)) *
        (traceRight rho ⊗ₖ traceLeft rho) := by
      rw [← mul_kronecker_mul, pinvX hA, pinvX hB]
    rw [this, ← mulVec_mulVec, hv, mulVec_zero]
  have h2 : rho = rho * (PA ⊗ₖ PB) := by
    have : (1 : Matrix (K × L) (K × L) ℂ) = (1 - PA) ⊗ₖ (1 : Matrix L L ℂ) +
        ((1 : Matrix K K ℂ) ⊗ₖ (1 - PB)) * (PA ⊗ₖ (1 : Matrix L L ℂ)) + PA ⊗ₖ PB := by
      rw [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, sub_kronecker, kronecker_sub,
        one_kronecker_one]
      abel
    conv_lhs => rw [← Matrix.mul_one rho, this]
    rw [Matrix.mul_add, Matrix.mul_add, kill_A hr, ← Matrix.mul_assoc, kill_B hr, Matrix.zero_mul,
      zero_add, zero_add]
  rw [h2, ← mulVec_mulVec, h1, mulVec_zero]

lemma Dr_eq : Dr rho (traceRight rho ⊗ₖ traceLeft rho) =
    entropy (traceRight rho) + entropy (traceLeft rho) - entropy rho := by
  have hA := (tr_density hr).1.1
  have hB := (tl_density hr).1.1
  rw [Dr_split, tr_logσ hr, Complex.add_re]
  unfold entropy
  rw [xlogx hA, xlogx hB]
  ring

theorem subadd : entropy rho ≤ entropy (traceRight rho) + entropy (traceLeft rho) ∧
    (entropy rho = entropy (traceRight rho) + entropy (traceLeft rho) ↔
      rho = traceRight rho ⊗ₖ traceLeft rho) := by
  have k := klein hr (σ_dens hr) (σ_ker hr)
  rw [Dr_eq hr] at k
  refine ⟨by linarith, fun h => ?_, fun h => ?_⟩
  · refine X5SK.klein_eq hr (σ_dens hr) (σ_ker hr) ?_
    rw [Dr_eq hr]; linarith
  · have h0 := Dr_self hr.1.1
    have e := Dr_eq hr
    rw [← h] at e
    linarith

end

end X5EP
end X5mod_EP_Sub

section X5mod_MN_Supp
open Matrix

namespace X5MN
open QAlgorithms.Papers.Independent.Information100.P07 (support operatorRange projection)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- indicator of nonzero eigenvalues -/
noncomputable def ind : ℝ → ℝ := fun x => if x = 0 then 0 else 1

lemma support_eq {X : Matrix I I ℂ} (hX : X.IsHermitian) : support X = cfc ind X := by
  have hsa := hX.isSelfAdjoint
  have fin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ X) := fun f =>
    (Matrix.finite_real_spectrum (A := X)).continuousOn f
  set P := cfc ind X
  set Q := cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) X
  have hXQ : X * Q = P := by
    have : P = cfc (fun x : ℝ => x * (if x = 0 then 0 else x⁻¹)) X := by
      refine cfc_congr fun x _ => ?_
      simp only [ind]; split_ifs with h
      · simp
      · field_simp
    rw [this, cfc_mul (fun x : ℝ => x) _ X (fin _) (fin _), cfc_id' ℝ X]
  have hPX : P * X = X := by
    rw [show P * X = P * cfc (fun x : ℝ => x) X by rw [cfc_id' ℝ X], ← cfc_mul ind (fun x : ℝ => x) X (fin _) (fin _)]
    conv_rhs => rw [← cfc_id' ℝ X]
    refine cfc_congr fun x _ => ?_
    simp only [ind]; split_ifs with h <;> simp [h]
  have hPh : Pᴴ = P := (cfc_predicate ind X : IsSelfAdjoint P)
  unfold support projection operatorRange
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.coe_coe]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine ⟨toEuclideanLin Q x, ?_⟩
    simp only [toLpLin_apply, WithLp.ofLp_toLp, mulVec_mulVec, hXQ]
  · rintro _ ⟨y, rfl⟩
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_sub, star_sub, star_mulVec, hPh,
      dotProduct_sub]
    rw [dotProduct_comm (X *ᵥ _) (star (WithLp.ofLp x) ᵥ* P), ← dotProduct_mulVec, mulVec_mulVec, hPX,
      dotProduct_comm]
    simp
end X5MN
end X5mod_MN_Supp

section X5mod_EV_Scalar
open Finset Set

namespace X5EV

variable {ι κ : Type} [Fintype ι] [Fintype κ]

noncomputable def ind : ℝ → ℝ := fun x => if x = 0 then 0 else 1

section
variable (a : ι → ℝ) (p : κ → ℝ) (w : ι → κ → ℝ)

noncomputable def Yv : ℝ := ∑ i, ∑ k, Real.exp (a i) * ind (p k) * w i k
noncomputable def Rv : ℝ := ∑ i, ∑ k, a i * p k * w i k
noncomputable def Sv : ℝ := -∑ k, p k * Real.log (p k)
noncomputable def xv (k : κ) : ℝ := ∑ i, w i k * a i
noncomputable def yv (k : κ) : ℝ := ∑ i, w i k * Real.exp (a i)
noncomputable def Kset : Finset κ := univ.filter fun k => p k ≠ 0
end

variable {a : ι → ℝ} {p : κ → ℝ} {w : ι → κ → ℝ}

lemma sum_K {f : κ → ℝ} (hf : ∀ k, p k = 0 → f k = 0) : ∑ k ∈ Kset p, f k = ∑ k, f k :=
  Finset.sum_filter_of_ne fun k _ h => fun hk => h (hf k hk)

lemma memK {k : κ} (hk : k ∈ Kset p) : p k ≠ 0 := (mem_filter.1 hk).2

lemma Y_eq : Yv a p w = ∑ k ∈ Kset p, yv a w k := by
  have : Yv a p w = ∑ k, ind (p k) * yv a w k := by
    unfold Yv yv; rw [Finset.sum_comm]; refine sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine sum_congr rfl fun i _ => ?_; ring
  rw [this, ← sum_K (p := p) (f := fun k => ind (p k) * yv a w k) (by intro k hk; simp [ind, hk])]
  refine sum_congr rfl fun k hk => ?_
  simp [ind, memK hk]

lemma R_eq : Rv a p w = ∑ k ∈ Kset p, p k * xv a w k := by
  have : Rv a p w = ∑ k, p k * xv a w k := by
    unfold Rv xv; rw [Finset.sum_comm]; refine sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine sum_congr rfl fun i _ => ?_; ring
  rw [this, sum_K (p := p) (f := fun k => p k * xv a w k) (by intro k hk; simp [hk])]

lemma S_eq : Sv p = -∑ k ∈ Kset p, p k * Real.log (p k) := by
  unfold Sv; rw [sum_K (p := p) (f := fun k => p k * Real.log (p k)) (by intro k hk; simp [hk])]

variable (hw : ∀ i k, 0 ≤ w i k) (hcol : ∀ k, ∑ i, w i k = 1) (hp : ∀ k, 0 ≤ p k)
  (hp1 : ∑ k, p k = 1)

include hp1 in
lemma pK : ∑ k ∈ Kset p, p k = 1 := by
  rw [sum_K (p := p) (f := p) (fun k hk => hk), hp1]

include hp1 in
lemma Kne : (Kset p).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := pK hp1; rw [h, sum_empty] at this; norm_num at this

include hw hcol in
lemma J1 (k : κ) : Real.exp (xv a w k) ≤ yv a w k := by
  have := convexOn_exp.map_sum_le (t := univ) (w := fun i => w i k) (p := a)
    (fun i _ => hw i k) (hcol k) (fun i _ => mem_univ _)
  simpa [xv, yv, smul_eq_mul] using this

include hw hcol in
lemma J1_eq {k : κ} (h : Real.exp (xv a w k) = yv a w k) {i : ι} (hi : w i k ≠ 0) :
    a i = xv a w k := by
  have e := (strictConvexOn_exp.map_sum_eq_iff_of_nonneg (t := univ) (w := fun i => w i k) (p := a)
    (fun i _ => hw i k) (hcol k) (fun i _ => mem_univ _)).1 (by simpa [xv, yv, smul_eq_mul] using h)
  have : xv a w k = ∑ j, w j k * a i := by
    unfold xv; refine sum_congr rfl fun j _ => ?_
    by_cases hj : w j k = 0
    · simp [hj]
    · rw [e (mem_univ j) hj (mem_univ i) hi]
  rw [this, ← Finset.sum_mul, hcol k, one_mul]

include hp hp1 in
lemma J2 : ∑ k ∈ Kset p, p k * (xv a w k - Real.log (p k)) ≤
    Real.log (∑ k ∈ Kset p, Real.exp (xv a w k)) := by
  have hpos : ∀ k ∈ Kset p, 0 < p k := fun k hk => lt_of_le_of_ne (hp k) (memK hk).symm
  have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Kset p) (w := p)
    (p := fun k => Real.exp (xv a w k) / p k) (fun k hk => (hpos k hk).le) (pK hp1)
    (fun k hk => div_pos (Real.exp_pos _) (hpos k hk))
  simp only [smul_eq_mul] at this
  have e1 : ∑ k ∈ Kset p, p k * Real.log (Real.exp (xv a w k) / p k) =
      ∑ k ∈ Kset p, p k * (xv a w k - Real.log (p k)) := by
    refine sum_congr rfl fun k hk => ?_
    rw [Real.log_div (Real.exp_pos _).ne' (memK hk), Real.log_exp]
  have e2 : ∑ k ∈ Kset p, p k * (Real.exp (xv a w k) / p k) = ∑ k ∈ Kset p, Real.exp (xv a w k) := by
    refine sum_congr rfl fun k hk => ?_
    field_simp [memK hk]
  rwa [e1, e2] at this

include hw hcol hp hp1 in
theorem main_le : Sv p ≤ Real.log (Yv a p w) - Rv a p w := by
  have h2 := J2 (a := a) (w := w) hp hp1
  have hne := Kne hp1
  have h3 : Real.log (∑ k ∈ Kset p, Real.exp (xv a w k)) ≤ Real.log (Yv a p w) := by
    rw [Y_eq]
    exact Real.log_le_log (sum_pos (fun k _ => Real.exp_pos _) hne)
      (sum_le_sum fun k _ => J1 hw hcol k)
  have e : ∑ k ∈ Kset p, p k * (xv a w k - Real.log (p k)) = Rv a p w + Sv p := by
    rw [R_eq, S_eq]; simp only [mul_sub, sum_sub_distrib]; ring
  linarith

include hw hcol hp hp1 in
theorem main_eq : Sv p = Real.log (Yv a p w) - Rv a p w ↔
    ∃ c : ℝ, ∀ i k, p k ≠ 0 → w i k ≠ 0 → a i = Real.log (p k) + c := by
  have hne := Kne hp1
  have hpos : ∀ k ∈ Kset p, 0 < p k := fun k hk => lt_of_le_of_ne (hp k) (memK hk).symm
  have e : ∑ k ∈ Kset p, p k * (xv a w k - Real.log (p k)) = Rv a p w + Sv p := by
    rw [R_eq, S_eq]; simp only [mul_sub, sum_sub_distrib]; ring
  constructor
  · intro heq
    have h2 := J2 (a := a) (w := w) hp hp1
    have hY := Y_eq (a := a) (p := p) (w := w)
    have hle : ∑ k ∈ Kset p, Real.exp (xv a w k) ≤ ∑ k ∈ Kset p, yv a w k :=
      sum_le_sum fun k _ => J1 hw hcol k
    have hpos1 : 0 < ∑ k ∈ Kset p, Real.exp (xv a w k) := sum_pos (fun k _ => Real.exp_pos _) hne
    have h3 : Real.log (∑ k ∈ Kset p, Real.exp (xv a w k)) ≤ Real.log (Yv a p w) := by
      rw [hY]; exact Real.log_le_log hpos1 hle
    -- both inequalities are equalities
    have q3 : Real.log (∑ k ∈ Kset p, Real.exp (xv a w k)) = Real.log (Yv a p w) := by linarith
    have q2 : ∑ k ∈ Kset p, p k * (xv a w k - Real.log (p k)) =
        Real.log (∑ k ∈ Kset p, Real.exp (xv a w k)) := by linarith
    have s3 : ∑ k ∈ Kset p, Real.exp (xv a w k) = ∑ k ∈ Kset p, yv a w k := by
      rw [← hY]; exact Real.log_injOn_pos hpos1 (by rw [hY]; exact lt_of_lt_of_le hpos1 hle) q3
    have each := (Finset.sum_eq_sum_iff_of_le fun k _ => J1 hw hcol k).1 s3
    -- Jensen equality for log
    have je := (strictConcaveOn_log_Ioi.map_sum_eq_iff_of_pos (t := Kset p) (w := p)
      (p := fun k => Real.exp (xv a w k) / p k) hpos (pK hp1)
      (fun k hk => div_pos (Real.exp_pos _) (hpos k hk))).1 (by
        simp only [smul_eq_mul]
        have e1 : ∑ k ∈ Kset p, p k * Real.log (Real.exp (xv a w k) / p k) =
            ∑ k ∈ Kset p, p k * (xv a w k - Real.log (p k)) := by
          refine sum_congr rfl fun k hk => ?_
          rw [Real.log_div (Real.exp_pos _).ne' (memK hk), Real.log_exp]
        have e2 : ∑ k ∈ Kset p, p k * (Real.exp (xv a w k) / p k) =
            ∑ k ∈ Kset p, Real.exp (xv a w k) := by
          refine sum_congr rfl fun k hk => ?_
          field_simp [memK hk]
        rw [e1, e2, q2])
    obtain ⟨k0, hk0⟩ := hne
    refine ⟨xv a w k0 - Real.log (p k0), fun i k hk hik => ?_⟩
    have kK : k ∈ Kset p := mem_filter.2 ⟨mem_univ _, hk⟩
    have := je kK hk0
    have l := congrArg Real.log this
    rw [Real.log_div (Real.exp_pos _).ne' hk, Real.log_div (Real.exp_pos _).ne' (memK hk0),
      Real.log_exp, Real.log_exp] at l
    rw [J1_eq hw hcol (each k kK) hik]; linarith
  · rintro ⟨c, hc⟩
    have hx : ∀ k ∈ Kset p, xv a w k = Real.log (p k) + c := by
      intro k hk
      unfold xv
      rw [show ∑ i, w i k * a i = ∑ i, w i k * (Real.log (p k) + c) from
        sum_congr rfl fun i _ => by
          by_cases hi : w i k = 0
          · simp [hi]
          · rw [hc i k (memK hk) hi]]
      rw [← sum_mul, hcol k, one_mul]
    have hy : ∀ k ∈ Kset p, yv a w k = p k * Real.exp c := by
      intro k hk
      unfold yv
      rw [show ∑ i, w i k * Real.exp (a i) = ∑ i, w i k * Real.exp (Real.log (p k) + c) from
        sum_congr rfl fun i _ => by
          by_cases hi : w i k = 0
          · simp [hi]
          · rw [hc i k (memK hk) hi]]
      rw [← sum_mul, hcol k, one_mul, Real.exp_add, Real.exp_log (hpos k hk)]
    have hY : Yv a p w = Real.exp c := by
      rw [Y_eq, sum_congr rfl hy, ← sum_mul, pK hp1, one_mul]
    have hR : Rv a p w = ∑ k ∈ Kset p, p k * Real.log (p k) + c := by
      rw [R_eq, sum_congr rfl fun k hk => by rw [hx k hk], ]
      simp only [mul_add, sum_add_distrib, ← sum_mul, pK hp1, one_mul]
    rw [hY, Real.log_exp, hR, S_eq]; ring

end X5EV
end X5mod_EV_Scalar

section X5mod_EV_Mat
open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5EVM
open X5DP X5RM X5EV
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I]

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cm (X : Matrix I I ℂ) (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (fin _ _) (fin _ _)).symm

lemma cfc_U {X : Matrix I I ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix I I ℂ) *
      diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hX.eigenvalues) *
        star (hX.eigenvectorUnitary : Matrix I I ℂ) := by
  rw [hX.cfc_eq]; unfold IsHermitian.cfc; rw [Unitary.conjStarAlgAut_apply]

lemma re_sum2 (F : I → I → ℝ) : (∑ i, ∑ k, ((F i k : ℝ) : ℂ)).re = ∑ i, ∑ k, F i k := by
  simp [Complex.re_sum]

section
variable {A R : Matrix I I ℂ} (hA : A.IsHermitian) (hR : QAlgorithms.IsDensityMatrix R)

lemma Y_tr : (NormedSpace.exp A * support R).trace.re =
    Yv hA.eigenvalues hR.1.1.eigenvalues (X5OL.w hA hR.1.1) := by
  rw [X5MN.support_eq hR.1.1, ← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  rw [show cfc X5MN.ind R = cfc X5EV.ind R from rfl, X5OL.tr_cfc_cfc hA hR.1.1, re_sum2]
  rfl

lemma R_tr : (A * R).trace.re = Rv hA.eigenvalues hR.1.1.eigenvalues (X5OL.w hA hR.1.1) := by
  have : A * R = cfc (fun x : ℝ => x) A * cfc (fun x : ℝ => x) R := by
    rw [cfc_id' ℝ A, cfc_id' ℝ R hR.1.1.isSelfAdjoint]
  rw [this, X5OL.tr_cfc_cfc hA hR.1.1, re_sum2]
  rfl

lemma S_ent : entropy R = Sv hR.1.1.eigenvalues := by
  unfold entropy Sv; rw [tr_cfc hR.1.1]

lemma hcol (k : I) : ∑ i, X5OL.w hA hR.1.1 i k = 1 := w_col hA hR.1.1 k

lemma hp1 : ∑ k, hR.1.1.eigenvalues k = 1 := by
  rw [sum_eig, hR.2]; simp

/-- matrix form of the equality condition -/
lemma cond_iff (c : ℝ) : A * cfc X5MN.ind R = cfc Real.log R + (c : ℂ) • cfc X5MN.ind R ↔
    ∀ i k, hR.1.1.eigenvalues k ≠ 0 → X5OL.w hA hR.1.1 i k ≠ 0 →
      hA.eigenvalues i = Real.log (hR.1.1.eigenvalues k) + c := by
  have hR1 := hR.1.1
  set U := (hA.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hR1.eigenvectorUnitary : Matrix I I ℂ)
  set O := X5OL.ov hA hR1
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2
  have hUU' : star U * U = 1 := Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
  have hVV : star V * V = 1 := Unitary.star_mul_self_of_mem (hR1.eigenvectorUnitary).2
  have hVV' : V * star V = 1 := Unitary.mul_star_self_of_mem (hR1.eigenvectorUnitary).2
  have hV : V = U * O := by
    simp only [O, X5OL.ov, U, V]; rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  set Da := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)
  set Di := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ X5MN.ind ∘ hR1.eigenvalues)
  set Dl := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ Real.log ∘ hR1.eigenvalues)
  have eA : A = U * Da * star U := by
    conv_lhs => rw [← cfc_id' ℝ A]
    rw [cfc_U hA]; rfl
  have eR : ∀ f : ℝ → ℝ, cfc f R = V * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR1.eigenvalues) *
      star V := fun f => cfc_U hR1 f
  have hO : star U * V = O := rfl
  have lhs : A * cfc X5MN.ind R = U * (Da * O * Di) * star V := by
    rw [eA, eR, ← hO]; simp only [Matrix.mul_assoc]; rfl
  have rhs : cfc Real.log R + (c : ℂ) • cfc X5MN.ind R = U * (O * (Dl + (c : ℂ) • Di)) * star V := by
    rw [← Matrix.mul_assoc U O, ← hV, eR, eR]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  rw [lhs, rhs]
  have inj : ∀ X Y : Matrix I I ℂ, U * X * star V = U * Y * star V ↔ X = Y := by
    intro X Y; constructor
    · intro h
      have := congrArg (fun Z => star U * Z * V) h
      simp only [Matrix.mul_assoc] at this
      rwa [hVV, ← Matrix.mul_assoc, hUU', Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        hUU', Matrix.one_mul, Matrix.mul_one] at this
    · rintro rfl; rfl
  rw [inj]
  constructor
  · intro h i k hk hw
    have e := congrFun (congrFun h i) k
    simp only [Da, Di, Dl, mul_diagonal, diagonal_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply,
      Matrix.smul_apply, Function.comp_apply, X5MN.ind, if_neg hk, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal] at e
    have hO : O i k ≠ 0 := by
      intro h0; apply hw; simp [X5OL.w, O, h0]
    have : ((hA.eigenvalues i : ℝ) : ℂ) = ((Real.log (hR1.eigenvalues k) + c : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hO
      push_cast at e ⊢
      linear_combination e
    exact_mod_cast this
  · intro h
    ext i k
    simp only [Da, Di, Dl, mul_diagonal, diagonal_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply,
      Matrix.smul_apply, Function.comp_apply, X5MN.ind, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal]
    by_cases hk : hR1.eigenvalues k = 0
    · simp [hk]
    by_cases h0 : O i k = 0
    · simp [h0]
    have hw : X5OL.w hA hR1 i k ≠ 0 := by
      simp only [X5OL.w]; exact pow_ne_zero _ (norm_ne_zero_iff.2 h0)
    rw [h i k hk hw]
    simp only [if_neg hk]
    push_cast
    ring

end

end X5EVM
end X5mod_EV_Mat

section X5mod_EV_Thm
open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5EVM
open X5DP X5RM X5EV
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I]

section
variable {R : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R)
include hR

lemma P_facts : support R * support R = support R ∧ support R * logMat R = logMat R ∧
    logMat R * support R = logMat R ∧ (support R)ᴴ = support R ∧ (logMat R)ᴴ = logMat R := by
  have hP := X5MN.support_eq hR.1.1
  have hL : logMat R = cfc Real.log R := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hP, cm]; refine cfc_congr fun x _ => ?_; simp only [X5MN.ind]; split_ifs <;> simp
  · rw [hP, hL, cm]; refine cfc_congr fun x _ => ?_; simp only [X5MN.ind]; split_ifs with h <;> simp [h]
  · rw [hP, hL, cm]; refine cfc_congr fun x _ => ?_; simp only [X5MN.ind]; split_ifs with h <;> simp [h]
  · rw [hP]; exact (cfc_predicate X5MN.ind R : IsSelfAdjoint _)
  · rw [hL]; exact (cfc_predicate Real.log R : IsSelfAdjoint _)

lemma cond_iff2 {A : Matrix I I ℂ} (hA : A.IsHermitian) (c : ℝ) :
    A * support R = logMat R + (c : ℂ) • support R ↔
      A * support R = support R * A ∧ support R * A * support R = logMat R + (c : ℂ) • support R := by
  obtain ⟨PP, PL, LP, PH, LH⟩ := P_facts hR
  set P := support R
  set L := logMat R
  constructor
  · intro h
    have hPA : P * A = A * P := by
      have := congrArg conjTranspose h
      rw [conjTranspose_mul, PH, hA.eq, conjTranspose_add, conjTranspose_smul, LH, PH] at this
      rw [this, h]; simp
    refine ⟨hPA.symm, ?_⟩
    rw [Matrix.mul_assoc, h, Matrix.mul_add, PL, Matrix.mul_smul, PP]
  · rintro ⟨h1, h2⟩
    rw [← h2, ← h1, Matrix.mul_assoc, PP]

theorem part1 :
    (∀ A : Matrix I I ℂ, A.IsHermitian → entropy R ≤
        Real.log (ev (support R) (NormedSpace.exp A)) - ev R A) ∧
    (∃ A : Matrix I I ℂ, A.IsHermitian ∧ entropy R =
        Real.log (ev (support R) (NormedSpace.exp A)) - ev R A) ∧
    (∀ A : Matrix I I ℂ, A.IsHermitian →
      (entropy R = Real.log (ev (support R) (NormedSpace.exp A)) - ev R A ↔
        ∃ c : ℝ, A * support R = support R * A ∧
          support R * A * support R = logMat R + (c : ℂ) • support R)) := by
  have hR1 := hR.1.1
  have key : ∀ A : Matrix I I ℂ, ∀ hA : A.IsHermitian,
      Real.log (ev (support R) (NormedSpace.exp A)) - ev R A =
        Real.log (Yv hA.eigenvalues hR1.eigenvalues (X5OL.w hA hR1)) -
          Rv hA.eigenvalues hR1.eigenvalues (X5OL.w hA hR1) := by
    intro A hA
    unfold ev QAlgorithms.effectProb
    rw [Y_tr hA hR, R_tr hA hR]
  have eqv : ∀ A : Matrix I I ℂ, A.IsHermitian →
      (entropy R = Real.log (ev (support R) (NormedSpace.exp A)) - ev R A ↔
        ∃ c : ℝ, A * support R = support R * A ∧
          support R * A * support R = logMat R + (c : ℂ) • support R) := by
    intro A hA
    rw [key A hA, S_ent hR, main_eq (X5OL.w_nonneg hA hR1) (hcol hA hR)
      (hR.1.eigenvalues_nonneg) (hp1 hR)]
    refine exists_congr fun c => ?_
    rw [← cond_iff hA hR c, ← cond_iff2 hR hA c, X5MN.support_eq hR1]
    rfl
  refine ⟨fun A hA => ?_, ⟨logMat R, (cfc_predicate Real.log R : IsSelfAdjoint _), ?_⟩, eqv⟩
  · rw [key A hA, S_ent hR]
    exact main_le (X5OL.w_nonneg hA hR1) (hcol hA hR) (hR.1.eigenvalues_nonneg) (hp1 hR)
  · have hLH : (logMat R).IsHermitian := (cfc_predicate Real.log R : IsSelfAdjoint _)
    refine (eqv _ hLH).2 ⟨0, ?_⟩
    exact (cond_iff2 hR hLH 0).1 (by rw [(P_facts hR).2.2.1]; simp)

end

section gibbs
variable [Nonempty I] {A : Matrix I I ℂ} (hA : A.IsHermitian)
include hA

lemma gs_eq : QAlgorithms.gibbsState A = σf A := by
  unfold QAlgorithms.gibbsState σf
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  have ht : (cfc Real.exp A).trace = ((Zf A : ℝ) : ℂ) := by
    refine Complex.ext rfl ?_
    have := (cfc_psd hA Real.exp fun x => (Real.exp_pos x).le).trace_nonneg
    simpa using (Complex.nonneg_iff.1 this).2.symm
  rw [ht, show (fun x => Real.exp x / Zf A) = fun x => (Zf A)⁻¹ * Real.exp x by
    funext x; ring, cfc_const_mul _ _ A (fin _ _), ← Complex.ofReal_inv, Complex.coe_smul]

theorem part2 : QAlgorithms.IsDensityMatrix (QAlgorithms.gibbsState A) ∧
    (∀ rho : Matrix I I ℂ, QAlgorithms.IsDensityMatrix rho →
      ev rho A + entropy rho ≤ Real.log ((NormedSpace.exp A).trace.re) ∧
      (ev rho A + entropy rho = Real.log ((NormedSpace.exp A).trace.re) ↔
        rho = QAlgorithms.gibbsState A)) := by
  have hZ : (NormedSpace.exp A).trace.re = Zf A := by
    unfold Zf; rw [CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  have hev : ∀ rho : Matrix I I ℂ, ev rho A = (rho * A).trace.re := by
    intro rho; unfold ev QAlgorithms.effectProb; rw [Matrix.trace_mul_comm]
  rw [gs_eq hA, hZ]
  refine ⟨σ_dens hA, fun rho hr => ⟨?_, ?_⟩⟩
  · rw [hev]; exact gibbs_le hA hr
  · rw [hev]
    constructor
    · intro h
      have k : Dr rho (σf A) = 0 := by
        rw [Dr_split, tr_log_σ hA hr]; unfold entropy at h; linarith
      exact X5SK.klein_eq hr (σ_dens hA) (σ_ker hA rho) k
    · rintro rfl; exact gibbs_eq hA

end gibbs

end X5EVM
end X5mod_EV_Thm

section X5mod_EP_Basic
open Matrix Set
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace X5EP
set_option linter.unusedSectionVars false
open QAlgorithms X5RM
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)
open QAlgorithms.Papers.Independent.Next46.P23 (ev)

variable {I : Type} [Fintype I] [DecidableEq I]

lemma eig_le {R : Matrix I I ℂ} (hR : IsDensityMatrix R) (k : I) : hR.1.1.eigenvalues k ≤ 1 := by
  have h1 : ∑ i, hR.1.1.eigenvalues i = 1 := by rw [sum_eig, hR.2]; simp
  rw [← h1]
  exact Finset.single_le_sum (fun i _ => hR.1.eigenvalues_nonneg i) (Finset.mem_univ k)

lemma ent_sum {R : Matrix I I ℂ} (hR : IsDensityMatrix R) :
    entropy R = -∑ k, hR.1.1.eigenvalues k * Real.log (hR.1.1.eigenvalues k) := by
  unfold entropy; rw [tr_cfc hR.1.1]

lemma ent_nonneg {R : Matrix I I ℂ} (hR : IsDensityMatrix R) : 0 ≤ entropy R := by
  rw [ent_sum hR, neg_nonneg]
  exact Finset.sum_nonpos fun k _ => Real.mul_log_nonpos (hR.1.eigenvalues_nonneg k) (eig_le hR k)

lemma spec_sub {R : Matrix I I ℂ} (hR : IsDensityMatrix R) : spectrum ℝ R ⊆ Icc 0 1 := by
  intro x hx
  rw [hR.1.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨k, rfl⟩ := hx
  exact ⟨hR.1.eigenvalues_nonneg k, eig_le hR k⟩

theorem ent_cont : ContinuousOn (entropy : Matrix I I ℂ → ℝ) {R | IsDensityMatrix R} := by
  have hc := continuousOn_cfc (𝕜 := ℝ) (A := Matrix I I ℂ) (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
    (fun x : ℝ => x * Real.log x) (Real.continuous_mul_log.continuousOn)
  have hs : {R : Matrix I I ℂ | IsDensityMatrix R} ⊆
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Icc (0 : ℝ) 1} :=
    fun R hR => ⟨hR.1.1.isSelfAdjoint, spec_sub hR⟩
  have ht : Continuous fun M : Matrix I I ℂ => -(M.trace.re) :=
    (Complex.continuous_re.comp (continuous_id.matrix_trace)).neg
  exact ht.comp_continuousOn (hc.mono hs)

/-- the uniform state as an algebra-map image -/
lemma unif_eq : uniformDensity I = algebraMap ℝ (Matrix I I ℂ) ((Fintype.card I : ℝ)⁻¹) := by
  unfold uniformDensity
  rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]; push_cast; rfl

variable [Nonempty I]

lemma unif_dens : IsDensityMatrix (uniformDensity I) := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_⟩
  · rw [unif_eq, Algebra.algebraMap_eq_smul_one]
    exact PosSemidef.one.smul (inv_nonneg.2 hc.le)
  · unfold uniformDensity
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    field_simp

lemma unif_ker (R : Matrix I I ℂ) :
    LinearMap.ker (uniformDensity I).mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv
  unfold uniformDensity at hv
  rw [smul_mulVec, one_mulVec] at hv
  have hc : ((Fintype.card I : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  rw [(smul_eq_zero.1 hv).resolve_left hc]; exact Submodule.zero_mem _

lemma Dr_unif {R : Matrix I I ℂ} (hR : IsDensityMatrix R) :
    Dr R (uniformDensity I) = Real.log (Fintype.card I) - entropy R := by
  rw [Dr_split, unif_eq, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, hR.2, Real.log_inv]
  unfold entropy; simp
  rw [← Complex.natCast_log, Complex.ofReal_re]; ring

theorem ent_le {R : Matrix I I ℂ} (hR : IsDensityMatrix R) : entropy R ≤ Real.log (Fintype.card I) := by
  have := klein hR unif_dens (unif_ker R); rw [Dr_unif hR] at this; linarith

theorem ent_eq_log {R : Matrix I I ℂ} (hR : IsDensityMatrix R) :
    entropy R = Real.log (Fintype.card I) ↔ R = uniformDensity I := by
  constructor
  · intro h
    refine X5SK.klein_eq hR unif_dens (unif_ker R) ?_
    rw [Dr_unif hR]; linarith
  · rintro rfl
    have := Dr_self (unif_dens (I := I)).1.1
    rw [Dr_unif unif_dens] at this; linarith

theorem ent_zero {R : Matrix I I ℂ} (hR : IsDensityMatrix R) :
    entropy R = 0 ↔ ∃ psi : EuclideanSpace ℂ I, IsState psi ∧ R = pureDensity psi := by
  have hR1 := hR.1.1
  constructor
  · intro h
    rw [ent_sum hR, neg_eq_zero] at h
    have each := (Finset.sum_eq_zero_iff_of_nonpos fun k _ =>
      Real.mul_log_nonpos (hR.1.eigenvalues_nonneg k) (eig_le hR k)).1 h
    have h01 : ∀ k, hR1.eigenvalues k = 0 ∨ hR1.eigenvalues k = 1 := by
      intro k
      rcases mul_eq_zero.1 (each k (Finset.mem_univ k)) with h0 | h0
      · exact Or.inl h0
      · rcases Real.log_eq_zero.1 h0 with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · linarith [hR.1.eigenvalues_nonneg k]
    have hsum : ∑ i, hR1.eigenvalues i = 1 := by rw [sum_eig, hR.2]; simp
    obtain ⟨k, hk⟩ : ∃ k, hR1.eigenvalues k = 1 := by
      by_contra hne; push_neg at hne
      have : ∀ i, hR1.eigenvalues i = 0 := fun i => (h01 i).resolve_right (hne i)
      simp [this] at hsum
    have hoth : ∀ j, j ≠ k → hR1.eigenvalues j = 0 := by
      intro j hj
      refine (h01 j).resolve_right fun h1 => ?_
      have := Finset.add_le_sum (f := hR1.eigenvalues) (fun i _ => hR.1.eigenvalues_nonneg i)
        (Finset.mem_univ j) (Finset.mem_univ k) hj
      linarith
    refine ⟨hR1.eigenvectorBasis k, (hR1.eigenvectorBasis).orthonormal.1 k, ?_⟩
    have e := X5EVM.cfc_U hR1 (fun x => x)
    rw [cfc_id' ℝ R hR1.isSelfAdjoint] at e
    conv_lhs => rw [e]
    ext a b
    simp only [mul_apply, diagonal_apply, Function.comp_apply, star_apply, pureDensity, of_apply,
      IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [Finset.sum_eq_single k]
    · rw [hk]; simp [RCLike.star_def]
    · intro j _ hj; rw [hoth j hj]; simp
    · simp
  · rintro ⟨psi, hpsi, rfl⟩
    have hn : ∑ c, star (psi c) * psi c = 1 := by
      have h2 : ‖psi‖ ^ 2 = 1 := by rw [hpsi]; norm_num
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
      have : ∑ c, ((‖psi c‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast h2
      rw [← this]; refine Finset.sum_congr rfl fun c _ => ?_
      exact (Complex.conj_mul' _).trans (by push_cast; ring)
    have hid : IsIdempotentElem (pureDensity psi) := by
      unfold IsIdempotentElem; ext a b
      simp only [mul_apply, pureDensity, of_apply]
      calc ∑ c, psi a * (starRingEnd ℂ) (psi c) * (psi c * (starRingEnd ℂ) (psi b)) =
          psi a * (starRingEnd ℂ) (psi b) * ∑ c, star (psi c) * psi c := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [RCLike.star_def]; ring
        _ = _ := by rw [hn, mul_one]
    unfold entropy
    have : cfc (fun x : ℝ => x * Real.log x) (pureDensity psi) = cfc (fun _ : ℝ => (0 : ℝ)) (pureDensity psi) := by
      refine cfc_congr fun x hx => ?_
      rcases hid.spectrum_subset ℝ hx with h | h
      · simp [h]
      · simp only [Set.mem_singleton_iff] at h; simp [h]
    rw [this, cfc_const_zero]; simp

theorem ent_unitary {R : Matrix I I ℂ} (hR : IsDensityMatrix R) (U : Matrix.unitaryGroup I ℂ) :
    entropy ((U : Matrix I I ℂ) * R * (U : Matrix I I ℂ)ᴴ) = entropy R := by
  unfold entropy
  rw [← star_eq_conjTranspose, cfc_conj U.2 hR.1.1.isSelfAdjoint, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem U.2, Matrix.one_mul]

theorem ent_gibbs {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    entropy (gibbsState A) = Real.log ((NormedSpace.exp A).trace.re) - ev (gibbsState A) A := by
  have e := gibbs_eq hA
  have hZ : (NormedSpace.exp A).trace.re = Zf A := by
    unfold Zf; rw [CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  rw [X5EVM.gs_eq hA, hZ]
  unfold ev effectProb; rw [Matrix.trace_mul_comm]; linarith

end X5EP
end X5mod_EP_Basic

section X5mod_RV_Nt
open Matrix Polynomial

namespace X5RV

variable {I : Type} [Fintype I] [DecidableEq I]

section
variable {M P : Matrix I I ℂ} (hPM : P * M = M) (hMP : M * P = M) (hPP : P * P = P)
include hPM hMP hPP

lemma QM : (1 - P) * M = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPM, sub_self]
lemma MQ : M * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hMP, sub_self]

lemma npow (c : ℂ) (n : ℕ) : (M - c • (1 - P)) ^ n = M ^ n * P + (-c) ^ n • (1 - P) := by
  have QQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have QP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 - P) * (M ^ n * P) = 0 := by
      rcases n with _ | n
      · simp [QP]
      · rw [pow_succ', Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P), QM hPM hMP hPP, Matrix.zero_mul]
    have e1 : M * (M ^ n * P) = M ^ (n + 1) * P := by rw [← Matrix.mul_assoc, ← pow_succ']
    have e2 : M * ((-c) ^ n • (1 - P)) = 0 := by rw [Matrix.mul_smul, MQ hPM hMP hPP, smul_zero]
    have e3 : (c • (1 - P)) * (M ^ n * P) = 0 := by rw [Matrix.smul_mul, h1, smul_zero]
    have e4 : (c • (1 - P)) * ((-c) ^ n • (1 - P)) = (c * (-c) ^ n) • (1 - P) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, QQ, smul_smul]
    rw [pow_succ', ih, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4, pow_succ]
    module

lemma aeval_N (c : ℝ) (p : ℝ[X]) :
    aeval (M - ((c : ℝ) : ℂ) • (1 - P)) p = aeval M p * P + ((p.eval (-c) : ℝ) : ℂ) • (1 - P) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, Matrix.add_mul, eval_add, Complex.ofReal_add, add_smul]; abel
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, npow hPM hMP hPP, eval_monomial, Algebra.algebraMap_eq_smul_one]
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_add, ← Complex.coe_smul, smul_smul]
    push_cast; ring_nf

lemma fin' (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cfc_N (hM : M.IsHermitian) (hPH : Pᴴ = P) (c : ℝ) (f : ℝ → ℝ) :
    cfc f (M - ((c : ℝ) : ℂ) • (1 - P)) = cfc f M * P + ((f (-c) : ℝ) : ℂ) • (1 - P) := by
  have hN : (M - ((c : ℝ) : ℂ) • (1 - P)).IsHermitian := by
    refine hM.sub ?_
    unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, hPH]; simp
  have hf1 : (spectrum ℝ (M - ((c : ℝ) : ℂ) • (1 - P))).Finite := Matrix.finite_real_spectrum
  have hf2 : (spectrum ℝ M).Finite := Matrix.finite_real_spectrum
  set s : Finset ℝ := hf1.toFinset ∪ hf2.toFinset ∪ {-c}
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have e1 : cfc f (M - ((c : ℝ) : ℂ) • (1 - P)) = aeval (M - ((c : ℝ) : ℂ) • (1 - P)) p := by
    rw [← cfc_polynomial p _ hN.isSelfAdjoint]
    exact cfc_congr fun x hx => (hp x (by simp [s, hf1.mem_toFinset.2 hx])).symm
  have e2 : cfc f M = aeval M p := by
    rw [← cfc_polynomial p M hM.isSelfAdjoint]
    exact cfc_congr fun x hx => (hp x (by simp [s, hf2.mem_toFinset.2 hx])).symm
  rw [e1, e2, aeval_N hPM hMP hPP, hp (-c) (by simp [s])]

end

end X5RV
end X5mod_RV_Nt

section X5mod_SB_Scalar
open Finset Set

namespace X5SB

variable {ι : Type} [Fintype ι]

noncomputable def ind : ℝ → ℝ := fun x => if x = 0 then 0 else 1

section
variable {l m : ι → ℝ} {W : ι → ι → ℝ}
  (hW : ∀ i j, 0 ≤ W i j) (hcol : ∀ j, ∑ i, W i j = 1) (hl : ∀ j, 0 ≤ l j) (hl1 : ∑ j, l j = 1)
  (hm : ∀ i, 0 ≤ m i) (hs : ∀ i j, W i j ≠ 0 → l j ≠ 0 → m i ≠ 0)

noncomputable def T (l : ι → ℝ) (W : ι → ι → ℝ) : Finset (ι × ι) :=
  univ.filter fun p => W p.1 p.2 ≠ 0 ∧ l p.2 ≠ 0

lemma sumT {f : ι × ι → ℝ} (hf : ∀ p, W p.1 p.2 = 0 ∨ l p.2 = 0 → f p = 0) :
    ∑ p ∈ T l W, f p = ∑ i, ∑ j, f (i, j) := by
  rw [← Fintype.sum_prod_type]
  refine Finset.sum_filter_of_ne fun p _ h => ?_
  by_contra hc
  rw [not_and_or, not_not, not_not] at hc
  exact h (hf p hc)

include hW hcol hl hl1 in
lemma qsum : ∑ p ∈ T l W, W p.1 p.2 * l p.2 = 1 := by
  rw [sumT (f := fun p => W p.1 p.2 * l p.2) (by rintro p (h | h) <;> simp [h])]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hcol, one_mul, hl1]

include hl hm hs in
lemma pos {p : ι × ι} (hp : p ∈ T l W) : 0 < l p.2 ∧ 0 < m p.1 := by
  obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
  exact ⟨lt_of_le_of_ne (hl _) (Ne.symm h2), lt_of_le_of_ne (hm _) (Ne.symm (hs _ _ h1 h2))⟩

noncomputable def D (l m : ι → ℝ) (W : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (l j * Real.log (l j) - Real.log (m i) * l j) * W i j

include hl hm hs in
lemma D_T : D l m W = ∑ p ∈ T l W, W p.1 p.2 * l p.2 * (Real.log (l p.2) - Real.log (m p.1)) := by
  unfold D
  rw [sumT (f := fun p => W p.1 p.2 * l p.2 * (Real.log (l p.2) - Real.log (m p.1)))
    (by rintro p (h | h) <;> simp [h])]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

include hW hcol hl hl1 hm hs in
theorem low : -Real.log (∑ i, ∑ j, m i * ind (l j) * W i j) ≤ D l m W := by
  have hq := qsum hW hcol hl hl1
  have J := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := T l W)
    (w := fun p => W p.1 p.2 * l p.2) (p := fun p => m p.1 / l p.2)
    (fun p hp => mul_nonneg (hW _ _) (hl _)) hq
    (fun p hp => div_pos (pos hl hm hs hp).2 (pos hl hm hs hp).1)
  simp only [smul_eq_mul] at J
  have e1 : ∑ p ∈ T l W, W p.1 p.2 * l p.2 * Real.log (m p.1 / l p.2) = -D l m W := by
    rw [D_T hl hm hs, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨a, b⟩ := pos hl hm hs hp
    rw [Real.log_div b.ne' a.ne']; ring
  have e2 : ∑ p ∈ T l W, W p.1 p.2 * l p.2 * (m p.1 / l p.2) = ∑ i, ∑ j, m i * ind (l j) * W i j := by
    rw [← sumT (l := l) (W := W) (f := fun p => m p.1 * ind (l p.2) * W p.1 p.2) (by rintro p (h | h) <;> simp [h, ind])]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨a, b⟩ := pos hl hm hs hp
    simp only [ind, if_neg a.ne']; field_simp
  rw [e1, e2] at J; linarith

include hW hcol hl hl1 hm hs in
theorem up : D l m W ≤ Real.log (∑ i, ∑ j, W i j * l j ^ 2 / m i) := by
  have hq := qsum hW hcol hl hl1
  have J := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := T l W)
    (w := fun p => W p.1 p.2 * l p.2) (p := fun p => l p.2 / m p.1)
    (fun p hp => mul_nonneg (hW _ _) (hl _)) hq
    (fun p hp => div_pos (pos hl hm hs hp).1 (pos hl hm hs hp).2)
  simp only [smul_eq_mul] at J
  have e1 : ∑ p ∈ T l W, W p.1 p.2 * l p.2 * Real.log (l p.2 / m p.1) = D l m W := by
    rw [D_T hl hm hs]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨a, b⟩ := pos hl hm hs hp
    rw [Real.log_div a.ne' b.ne']
  have e2 : ∑ p ∈ T l W, W p.1 p.2 * l p.2 * (l p.2 / m p.1) = ∑ i, ∑ j, W i j * l j ^ 2 / m i := by
    rw [← sumT (l := l) (W := W) (f := fun p => W p.1 p.2 * l p.2 ^ 2 / m p.1) (by rintro p (h | h) <;> simp [h])]
    refine Finset.sum_congr rfl fun p hp => ?_
    ring
  rw [e1, e2] at J; exact J

end

end X5SB
end X5mod_SB_Scalar

section X5mod_SB_Thm
open Matrix Set
open scoped ComplexOrder

namespace X5SBM
open X5DP X5RM X5SB
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (dMin unnormalizedRelativeBits)

variable {I : Type} [Fintype I] [DecidableEq I]

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma incl_of_le {R S : Matrix I I ℂ} (hR : R.PosSemidef) {c : ℝ}
    (h : (((c : ℝ) : ℂ) • S - R).PosSemidef) : SupportIncluded R S := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have h1 := h.dotProduct_mulVec_nonneg v
  rw [sub_mulVec, smul_mulVec, hv, smul_zero, zero_sub, dotProduct_neg] at h1
  have h2 := hR.dotProduct_mulVec_nonneg v
  have h3 : star v ⬝ᵥ (R *ᵥ v) = 0 := le_antisymm (neg_nonneg.1 h1) h2
  exact (hR.dotProduct_mulVec_zero_iff v).1 h3

section
variable {R S : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R) (hS : QAlgorithms.IsDensityMatrix S)
  (hsupp : SupportIncluded R S)
include hR hS hsupp

lemma hs' : ∀ i j, X5OL.w hS.1.1 hR.1.1 i j ≠ 0 → hR.1.1.eigenvalues j ≠ 0 →
    hS.1.1.eigenvalues i ≠ 0 := by
  intro i j hw hl hm
  apply hw
  rw [w_swap hR.1.1 hS.1.1 j i]
  simp [X5OL.w, X5OL.supp_fwd hR.1.1 hS.1.1 hsupp j i hl hm]

lemma hl1' : ∑ j, hR.1.1.eigenvalues j = 1 := by rw [sum_eig, hR.2]; simp

/-- there is an overlapping pair with positive weights -/
lemma ex_pair : ∃ i j, X5OL.w hS.1.1 hR.1.1 i j ≠ 0 ∧ hR.1.1.eigenvalues j ≠ 0 := by
  have h1 := hl1' hR hS hsupp
  obtain ⟨j, hj⟩ : ∃ j, hR.1.1.eigenvalues j ≠ 0 := by
    by_contra h; push_neg at h; simp [h] at h1
  have h2 := w_col hS.1.1 hR.1.1 j
  obtain ⟨i, hi⟩ : ∃ i, X5OL.w hS.1.1 hR.1.1 i j ≠ 0 := by
    by_contra h; push_neg at h; simp [h] at h2
  exact ⟨i, j, hi, hj⟩

lemma trP : tr (support R * S) = ∑ i, ∑ j, hS.1.1.eigenvalues i * X5SB.ind (hR.1.1.eigenvalues j) *
    X5OL.w hS.1.1 hR.1.1 i j := by
  unfold tr
  rw [X5MN.support_eq hR.1.1, Matrix.trace_mul_comm]
  have : S * cfc X5MN.ind R = cfc (fun x : ℝ => x) S * cfc X5SB.ind R := by
    rw [cfc_id' ℝ S hS.1.1.isSelfAdjoint]; rfl
  rw [this, X5OL.tr_cfc_cfc hS.1.1 hR.1.1]
  simp [Complex.re_sum]

lemma trP_pos : 0 < tr (support R * S) := by
  rw [trP hR hS hsupp]
  obtain ⟨i, j, hi, hj⟩ := ex_pair hR hS hsupp
  have hm := hs' hR hS hsupp i j hi hj
  have nn : ∀ a b, 0 ≤ hS.1.1.eigenvalues a * X5SB.ind (hR.1.1.eigenvalues b) * X5OL.w hS.1.1 hR.1.1 a b :=
    fun a b => mul_nonneg (mul_nonneg (hS.1.eigenvalues_nonneg a) (by unfold X5SB.ind; split_ifs <;> norm_num))
      (X5OL.w_nonneg _ _ _ _)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => nn a b)
    (Finset.mem_univ i))
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b _ => nn i b) (Finset.mem_univ j))
  simp only [X5SB.ind, if_neg hj, mul_one]
  exact mul_pos (lt_of_le_of_ne (hS.1.eigenvalues_nonneg i) (Ne.symm hm))
    (lt_of_le_of_ne (X5OL.w_nonneg _ _ _ _) (Ne.symm hi))

noncomputable def Gp : ℝ := ∑ i, ∑ j, X5OL.w hS.1.1 hR.1.1 i j * hR.1.1.eigenvalues j ^ 2 / hS.1.1.eigenvalues i

lemma Gp_pos : 0 < Gp hR hS := by
  obtain ⟨i, j, hi, hj⟩ := ex_pair hR hS hsupp
  have hm := hs' hR hS hsupp i j hi hj
  have nn : ∀ a b, 0 ≤ X5OL.w hS.1.1 hR.1.1 a b * hR.1.1.eigenvalues b ^ 2 / hS.1.1.eigenvalues a :=
    fun a b => div_nonneg (mul_nonneg (X5OL.w_nonneg _ _ _ _) (sq_nonneg _)) (hS.1.eigenvalues_nonneg a)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => nn a b)
    (Finset.mem_univ i))
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b _ => nn i b) (Finset.mem_univ j))
  exact div_pos (mul_pos (lt_of_le_of_ne (X5OL.w_nonneg _ _ _ _) (Ne.symm hi)) (pow_pos
    (lt_of_le_of_ne (hR.1.eigenvalues_nonneg j) (Ne.symm hj)) 2))
    (lt_of_le_of_ne (hS.1.eigenvalues_nonneg i) (Ne.symm hm))

lemma Gp_eq : Gp hR hS = G 0 1 hR.1.1 hS.1.1 := by
  unfold Gp G
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [w_swap hR.1.1 hS.1.1 j i]; ring_nf

lemma G_le {c : ℝ} (hc : 0 < c) (h : (((c : ℝ) : ℂ) • S - R).PosSemidef) : Gp hR hS ≤ c := by
  rw [Gp_eq hR hS hsupp]
  obtain ⟨Z, hZ⟩ := var_eq 0 1 hR.1.1 hS.1.1
  rw [← hZ]
  have hR1 := hR.1.1
  have step1 : val 0 1 R S Z ≤ val 0 c⁻¹ R R Z := by
    unfold val
    have p := (h.mul_mul_conjTranspose_same Z).trace_nonneg
    have p' : 0 ≤ (Z * (((c : ℝ) : ℂ) • S - R) * Zᴴ).trace.re := (Complex.nonneg_iff.1 p).1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at p'
    have : c⁻¹ * (Z * R * Zᴴ).trace.re ≤ (Z * S * Zᴴ).trace.re := by
      rw [inv_mul_le_iff₀ hc]; linarith
    linarith
  have hs2 : ∀ a b, 0 * hR.1.1.eigenvalues a + c⁻¹ * hR.1.1.eigenvalues b = 0 →
      (hR.1.1.eigenvalues a : ℂ) * X5OL.ov hR.1.1 hR.1.1 a b = 0 := by
    intro a b hab
    have hb : hR.1.1.eigenvalues b = 0 := by
      simp only [zero_mul, zero_add, mul_eq_zero, inv_eq_zero] at hab
      exact hab.resolve_left hc.ne'
    have ho : X5OL.ov hR.1.1 hR.1.1 = 1 :=
      Unitary.star_mul_self_of_mem (hR.1.1.eigenvectorUnitary).2
    rw [ho, one_apply]
    split_ifs with hab'
    · subst hab'; simp [hb]
    · simp
  have step2 := var_le 0 c⁻¹ le_rfl (inv_nonneg.2 hc.le) hR.1 hR.1 hs2 Z
  have step3 : G 0 c⁻¹ hR.1.1 hR.1.1 = c := by
    unfold G
    have e : ∀ a, ∑ b, X5OL.w hR.1.1 hR.1.1 a b * hR.1.1.eigenvalues a ^ 2 /
        (0 * hR.1.1.eigenvalues a + c⁻¹ * hR.1.1.eigenvalues b) =
        c * hR.1.1.eigenvalues a := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [w_self, if_pos rfl]
        by_cases h0 : hR.1.1.eigenvalues a = 0
        · simp [h0]
        · field_simp; ring
      · intro b _ hb; rw [w_self, if_neg (Ne.symm hb)]; simp
      · simp
    simp only [e, ← Finset.mul_sum]
    have := hl1' hR hS hsupp
    rw [this, mul_one]
  calc val 0 1 R S Z ≤ val 0 c⁻¹ R R Z := step1
    _ ≤ G 0 c⁻¹ hR.1.1 hR.1.1 := step2
    _ = c := step3

lemma Dr_eq : Dr R S = D hR.1.1.eigenvalues hS.1.1.eigenvalues (X5OL.w hS.1.1 hR.1.1) := by
  rw [D_sum hR.1.1 hS.1.1]; rfl

end

lemma bits_eq {R S : Matrix I I ℂ} (hR : R.IsHermitian) :
    tr (R * (cfc (fun x : ℝ => Real.logb 2 x) R - cfc (fun x : ℝ => Real.logb 2 x) S)) =
      Dr R S / Real.log 2 := by
  have e : ∀ X : Matrix I I ℂ, cfc (fun x : ℝ => Real.logb 2 x) X = (Real.log 2)⁻¹ • cfc Real.log X := by
    intro X
    rw [show (fun x : ℝ => Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * Real.log x by
      funext x; rw [Real.logb]; ring]
    exact cfc_const_mul _ _ X (fin _ _)
  have hx : R * cfc Real.log R = cfc (fun x : ℝ => x * Real.log x) R := by
    have : R * cfc Real.log R = cfc (fun x : ℝ => x) R * cfc Real.log R := by
      rw [cfc_id' ℝ R hR.isSelfAdjoint]
    rw [this, ← cfc_mul _ _ R (fin _ _) (fin _ _)]
  unfold tr Dr
  rw [e, e, ← smul_sub, Matrix.mul_smul, Matrix.mul_sub, hx, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.re_ofReal_mul]
  rw [div_eq_inv_mul]

theorem main [Nonempty I] (R S : Matrix I I ℂ) (hR : QAlgorithms.IsDensityMatrix R)
    (hS : QAlgorithms.IsDensityMatrix S) :
    dMin R S ≤ unnormalizedRelativeBits R S ∧ unnormalizedRelativeBits R S ≤ maxRelative R S := by
  by_cases hsupp : SupportIncluded R S
  · have hb : unnormalizedRelativeBits R S = ((Dr R S / Real.log 2 : ℝ) : EReal) := by
      unfold unnormalizedRelativeBits; rw [if_pos hsupp, bits_eq hR.1.1]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hD := Dr_eq hR hS hsupp
    have hW := fun i j => X5OL.w_nonneg hS.1.1 hR.1.1 i j
    have hcol := w_col hS.1.1 hR.1.1
    have hl := hR.1.eigenvalues_nonneg
    have hm := hS.1.eigenvalues_nonneg
    have hl1 := hl1' hR hS hsupp
    have hss := hs' hR hS hsupp
    rw [hb]
    constructor
    · have lo := low hW hcol hl hl1 hm hss
      rw [← hD, ← trP hR hS hsupp] at lo
      have hp := trP_pos hR hS hsupp
      unfold dMin elog
      rw [if_pos hp, ← EReal.coe_neg, EReal.coe_le_coe_iff, Real.logb, ← neg_div]
      exact div_le_div_of_nonneg_right lo hl2.le
    · unfold maxRelative
      refine le_sInf ?_
      rintro v ⟨L, rfl, hL⟩
      rw [EReal.coe_le_coe_iff]
      have u := up hW hcol hl hl1 hm hss
      rw [← hD] at u
      have g := G_le hR hS hsupp (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) L) hL
      have : Dr R S ≤ L * Real.log 2 := by
        calc Dr R S ≤ Real.log (Gp hR hS) := u
          _ ≤ Real.log ((2 : ℝ) ^ L) := Real.log_le_log (Gp_pos hR hS hsupp) g
          _ = L * Real.log 2 := by rw [Real.log_rpow (by norm_num)]
      rw [div_le_iff₀ hl2]; exact this
  · have hb : unnormalizedRelativeBits R S = ⊤ := by
      unfold unnormalizedRelativeBits; rw [if_neg hsupp]
    rw [hb]
    refine ⟨le_top, ?_⟩
    unfold maxRelative
    refine le_sInf ?_
    rintro v ⟨L, rfl, hL⟩
    exact (hsupp (incl_of_le hR.1 hL)).elim

end X5SBM
end X5mod_SB_Thm

section X5mod_MN_Thm
open Matrix Set
open scoped ComplexOrder

namespace X5MN
open X5DP X5RM
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (dMin)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma tr_supp {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    tr (support X * Y) = S X Y 0 := by
  unfold S QAlgorithms.Papers.Independent.Next46.P23.ev QAlgorithms.effectProb tr
  have e1 : supportPower Y (1 - 0) = Y := by
    unfold supportPower
    conv_rhs => rw [← cfc_id' ℝ Y hY.isSelfAdjoint]
    refine cfc_congr fun x _ => ?_
    by_cases h : x = 0
    · simp [h]
    · simp [h]
  have e0 : supportPower X 0 = cfc ind X := by
    unfold supportPower
    refine cfc_congr fun x _ => ?_
    by_cases h : x = 0
    · simp [h, ind]
    · simp [h, ind]
  rw [e1, e0, support_eq hX, Matrix.trace_mul_comm]

lemma elog_mono {x y : ℝ} (h : x ≤ y) : elog x ≤ elog y := by
  unfold elog
  split_ifs with h1 h2 h2
  · exact EReal.coe_le_coe_iff.2 (Real.logb_le_logb_of_le (by norm_num) h1 h)
  · exact absurd (lt_of_lt_of_le h1 h) h2
  · exact bot_le
  · exact le_rfl

theorem main (rho sigma : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (hsigma : sigma.PosSemidef) (T : QAlgorithms.Superop I J) (hT : QAlgorithms.IsChannel T) :
    dMin (T rho) (T sigma) ≤ dMin rho sigma ∧
    maxRelative (T rho) (T sigma) ≤ maxRelative rho sigma := by
  obtain ⟨m, E, hE, hTE⟩ := hT
  have hT' : ∀ X, T X = Φ E X := fun X => by rw [hTE]; rfl
  have hr' := Φ_psd E hrho
  have hs' := Φ_psd E hsigma
  constructor
  · unfold dMin
    rw [hT', hT', tr_supp hrho.1 hsigma.1, tr_supp hr'.1 hs'.1, EReal.neg_le_neg_iff]
    refine elog_mono ?_
    have key : Icc (0 : ℝ) 1 ⊆ {t | S rho sigma t ≤ S (Φ E rho) (Φ E sigma) t} := by
      have hc : IsClosed {t | S rho sigma t ≤ S (Φ E rho) (Φ E sigma) t} :=
        isClosed_le (S_cont hrho.1 hsigma.1) (S_cont hr'.1 hs'.1)
      have hsub : Ioo (0 : ℝ) 1 ⊆ {t | S rho sigma t ≤ S (Φ E rho) (Φ E sigma) t} := by
        intro t ht
        simp only [mem_ofPred_eq]
        rw [S_eq ht.1, S_eq ht.1]
        exact X5DP.Qf_lt t ht.1 ht.2 E hE hrho hsigma
      have := closure_minimal hsub hc
      rwa [closure_Ioo zero_ne_one] at this
    exact key ⟨le_rfl, zero_le_one⟩
  · unfold maxRelative
    refine sInf_le_sInf ?_
    rintro v ⟨l, rfl, h⟩
    refine ⟨l, rfl, ?_⟩
    rw [hT', hT']
    have : (((2 : ℝ) ^ l : ℝ) : ℂ) • Φ E sigma - Φ E rho =
        Φ E ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - rho) := by
      simp only [Φ, Finset.smul_sum, ← Finset.sum_sub_distrib, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [this]
    exact Φ_psd E h

end X5MN
end X5mod_MN_Thm

section X5mod_SB_L12
open Matrix Set
open scoped ComplexOrder

namespace X5L12
open X5DP X5RM X5SB X5SBM
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (dMin unnormalizedRelativeBits)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma cm (X : Matrix I I ℂ) (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (fin _ _) (fin _ _)).symm

/-- facts about the minimal positive eigenvalue -/
lemma mpe {S : Matrix I I ℂ} (hS : QAlgorithms.IsDensityMatrix S) :
    0 < QAlgorithms.minPositiveEigenvalue S ∧
      ∀ i, 0 < hS.1.1.eigenvalues i → QAlgorithms.minPositiveEigenvalue S ≤ hS.1.1.eigenvalues i := by
  have hS1 := hS.1.1
  set E := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I)) with hE
  have hasc : ∀ k, QAlgorithms.ascEigenvalues S k = hS1.eigenvalues₀ (Fin.rev k) := by
    intro k; unfold QAlgorithms.ascEigenvalues; rw [dif_pos hS1]
  have hev : ∀ i, hS1.eigenvalues i = QAlgorithms.ascEigenvalues S (Fin.rev (E.symm i)) := by
    intro i; rw [hasc, Fin.rev_rev]; rfl
  have h1 : ∑ i, hS1.eigenvalues i = 1 := by rw [sum_eig, hS.2]; simp
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < hS1.eigenvalues i := by
    by_contra h; push_neg at h
    have : ∑ i, hS1.eigenvalues i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  set s := Finset.univ.filter fun k => 0 < QAlgorithms.ascEigenvalues S k
  have hne : s.Nonempty := ⟨Fin.rev (E.symm i0), by simp [s, ← hev, hi0]⟩
  have hdef : QAlgorithms.minPositiveEigenvalue S = s.inf' hne (QAlgorithms.ascEigenvalues S) := by
    unfold QAlgorithms.minPositiveEigenvalue; rw [dif_pos hne]
  rw [hdef]
  constructor
  · obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' hne (QAlgorithms.ascEigenvalues S)
    rw [he]; exact (Finset.mem_filter.1 hk).2
  · intro i hi
    rw [hev i]
    exact Finset.inf'_le _ (by simp [s, ← hev, hi])

section
variable {R S : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R) (hS : QAlgorithms.IsDensityMatrix S)
  (hsupp : SupportIncluded R S)
include hR hS hsupp

lemma kill (M : Matrix I I ℂ) (h : S * M = 0) : R * M = 0 := by
  ext i j
  have hc : S *ᵥ (fun k => M k j) = 0 := by
    ext a; have := congrFun (congrFun h a) j; simpa [mulVec, dotProduct, mul_apply] using this
  have hc' : R *ᵥ (fun k => M k j) = 0 := by
    have := hsupp (show (fun k => M k j) ∈ LinearMap.ker S.mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply]; exact hc)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have := congrFun hc' i
  simpa [mulVec, dotProduct, mul_apply] using this

lemma RP : R * cfc X5EP.ind S = R := by
  have hS1 := hS.1.1
  have h0 : S * cfc (fun x => 1 - X5EP.ind x) S = 0 := by
    have : S * cfc (fun x => 1 - X5EP.ind x) S = cfc (fun x : ℝ => x) S * cfc (fun x => 1 - X5EP.ind x) S := by
      rw [cfc_id' ℝ S hS1.isSelfAdjoint]
    rw [this, cm, ← cfc_const_zero ℝ S]
    refine cfc_congr fun x _ => ?_
    simp only [X5EP.ind]; split_ifs with h <;> simp [h]
  have k := kill hR hS hsupp _ h0
  rw [cfc_sub _ _ S (fin _ _) (fin _ _), cfc_const_one ℝ S, Matrix.mul_sub, Matrix.mul_one,
    sub_eq_zero] at k
  exact k.symm

lemma PR : cfc X5EP.ind S * R = R := by
  have := congrArg conjTranspose (RP hR hS hsupp)
  rwa [conjTranspose_mul, X5EP.PH, hR.1.1.eq] at this

lemma one_sub_psd : (1 - R).PosSemidef := by
  have hR1 := hR.1.1
  have e : 1 - R = cfc (fun x : ℝ => max ((1 : ℝ) - x) 0) R := by
    rw [show (1 : Matrix I I ℂ) - R = cfc (fun x : ℝ => (1 : ℝ) - x) R by
      rw [cfc_sub _ _ R (fin _ _) (fin _ _), cfc_const_one ℝ R, cfc_id' ℝ R hR1.isSelfAdjoint]]
    refine cfc_congr fun x hx => ?_
    have := (X5EP.spec_sub hR hx).2
    rw [max_eq_left (by linarith)]
  rw [e]; exact cfc_psd hR1 _ fun x => le_max_right _ _

lemma P_sub_psd : (cfc X5EP.ind S - R).PosSemidef := by
  have e : cfc X5EP.ind S - R = (cfc X5EP.ind S)ᴴ * (1 - R) * cfc X5EP.ind S := by
    rw [X5EP.PH, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, X5EP.PP, PR hR hS hsupp,
      RP hR hS hsupp]
  rw [e]; exact (one_sub_psd hR hS hsupp).conjTranspose_mul_mul_same _

lemma scaled_psd : (((QAlgorithms.minPositiveEigenvalue S)⁻¹ : ℝ) : ℂ) • S - cfc X5EP.ind S
    |>.PosSemidef := by
  have hS1 := hS.1.1
  obtain ⟨hμ, hle⟩ := mpe hS
  set μ := QAlgorithms.minPositiveEigenvalue S
  have e : ((μ⁻¹ : ℝ) : ℂ) • S - cfc X5EP.ind S =
      cfc (fun x => if x = 0 then 0 else max (μ⁻¹ * x - 1) 0) S := by
    have : ((μ⁻¹ : ℝ) : ℂ) • S - cfc X5EP.ind S = cfc (fun x => μ⁻¹ * x - X5EP.ind x) S := by
      rw [cfc_sub _ _ S (fin _ _) (fin _ _), cfc_const_mul _ _ S (fin _ _), cfc_id' ℝ S hS1.isSelfAdjoint,
        Complex.coe_smul]
    rw [this]
    refine cfc_congr fun x hx => ?_
    rw [hS1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    by_cases h0 : hS1.eigenvalues i = 0
    · simp [h0, X5EP.ind]
    · have hp : 0 < hS1.eigenvalues i := lt_of_le_of_ne (hS.1.eigenvalues_nonneg i) (Ne.symm h0)
      have := hle i hp
      have : 1 ≤ μ⁻¹ * hS1.eigenvalues i := by rw [inv_mul_eq_div, le_div_iff₀ hμ]; linarith
      simp only [X5EP.ind, if_neg h0]; rw [max_eq_left (by linarith)]
  rw [e]; exact cfc_psd hS1 _ fun x => by split_ifs <;> simp

theorem clause2 : maxRelative R S ≤ -elog (QAlgorithms.minPositiveEigenvalue S) := by
  obtain ⟨hμ, -⟩ := mpe hS
  set μ := QAlgorithms.minPositiveEigenvalue S
  unfold elog; rw [if_pos hμ, ← EReal.coe_neg]
  unfold maxRelative
  refine sInf_le ⟨-Real.logb 2 μ, rfl, ?_⟩
  have h2 : (2 : ℝ) ^ (-Real.logb 2 μ) = μ⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hμ]
  rw [h2]
  have := (scaled_psd hR hS hsupp).add (P_sub_psd hR hS hsupp)
  rwa [sub_add_sub_cancel] at this

/-- trace of the support projector against the difference -/
lemma tr_le : tr (support R * (R - S)) ≤ QAlgorithms.traceNorm (R - S) / 2 := by
  have hD : (R - S).IsHermitian := hR.1.1.sub hS.1.1
  have hR1 := hR.1.1
  set l := hD.eigenvalues
  -- trace norm as a spectral sum
  have htn : QAlgorithms.traceNorm (R - S) = ∑ i, |l i| := by
    unfold QAlgorithms.traceNorm
    have e1 : (R - S)ᴴ * (R - S) = cfc (fun x : ℝ => x ^ 2) (R - S) := by
      rw [hD.eq, cfc_pow_id (R - S) 2 hD.isSelfAdjoint, sq]
    rw [e1, ← cfc_comp' Real.sqrt _ (R - S) (Real.continuous_sqrt.continuousOn) (fin _ _),
      tr_cfc hD]
    refine Finset.sum_congr rfl fun i _ => Real.sqrt_sq_eq_abs _
  have htr : ∑ i, l i = 0 := by
    rw [sum_eig, Matrix.trace_sub, hR.2, hS.2]; simp
  have hT : tr (support R * (R - S)) = ∑ i, l i * ∑ j, X5EP.ind (hR1.eigenvalues j) * X5OL.w hD hR1 i j := by
    unfold tr
    rw [X5MN.support_eq hR1, Matrix.trace_mul_comm]
    have : (R - S) * cfc X5MN.ind R = cfc (fun x : ℝ => x) (R - S) * cfc X5EP.ind R := by
      rw [cfc_id' ℝ (R - S) hD.isSelfAdjoint]; rfl
    rw [this, X5OL.tr_cfc_cfc hD hR1]
    simp only [Complex.re_sum, Complex.ofReal_re, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
  rw [hT, htn]
  have hc : ∀ i, 0 ≤ ∑ j, X5EP.ind (hR1.eigenvalues j) * X5OL.w hD hR1 i j ∧
      ∑ j, X5EP.ind (hR1.eigenvalues j) * X5OL.w hD hR1 i j ≤ 1 := by
    intro i
    have i01 : ∀ j, 0 ≤ X5EP.ind (hR1.eigenvalues j) ∧ X5EP.ind (hR1.eigenvalues j) ≤ 1 := by
      intro j; unfold X5EP.ind; split_ifs <;> norm_num
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (i01 j).1 (X5OL.w_nonneg _ _ _ _)
    · calc _ ≤ ∑ j, X5OL.w hD hR1 i j := Finset.sum_le_sum fun j _ =>
            mul_le_of_le_one_left (X5OL.w_nonneg _ _ _ _) (i01 j).2
        _ = 1 := X5OL.w_row hD hR1 i
  have key : ∀ i, l i * ∑ j, X5EP.ind (hR1.eigenvalues j) * X5OL.w hD hR1 i j ≤ (|l i| + l i) / 2 := by
    intro i
    obtain ⟨c0, c1⟩ := hc i
    rcases le_or_gt 0 (l i) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  calc _ ≤ ∑ i, (|l i| + l i) / 2 := Finset.sum_le_sum fun i _ => key i
    _ = (∑ i, |l i|) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib, htr, add_zero]

theorem clause3 : dMin R S ≤ -elog (1 - QAlgorithms.traceNorm (R - S) / 2) := by
  by_cases hpos : 0 < 1 - QAlgorithms.traceNorm (R - S) / 2
  · have t := tr_le hR hS hsupp
    have hPR : tr (support R * R) = 1 := by
      unfold tr; rw [X5MN.support_eq hR.1.1]
      have := PR hR hR (le_refl _)
      rw [show cfc X5MN.ind R = cfc X5EP.ind R from rfl, this, hR.2]; simp
    have hsplit : tr (support R * (R - S)) = tr (support R * R) - tr (support R * S) := by
      unfold tr; rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    have hge : 1 - QAlgorithms.traceNorm (R - S) / 2 ≤ tr (support R * S) := by linarith
    unfold dMin
    exact EReal.neg_le_neg_iff.2 (X5MN.elog_mono hge)
  · unfold elog; rw [if_neg hpos]; simp

end

end X5L12
end X5mod_SB_L12

section X5mod_SP_Thm
open Matrix Set
open scoped ComplexOrder

namespace X5SP
open X5DP X5RM
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (dMin largestEigenvalue)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma range_asc {R : Matrix I I ℂ} (hR : R.IsHermitian) :
    Set.range (QAlgorithms.ascEigenvalues R) = Set.range hR.eigenvalues := by
  set E := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))
  have hasc : ∀ k, QAlgorithms.ascEigenvalues R k = hR.eigenvalues₀ (Fin.rev k) := by
    intro k; unfold QAlgorithms.ascEigenvalues; rw [dif_pos hR]
  ext x; constructor
  · rintro ⟨k, rfl⟩
    refine ⟨E (Fin.rev k), ?_⟩
    rw [hasc]; show hR.eigenvalues₀ (E.symm (E (Fin.rev k))) = _; rw [Equiv.symm_apply_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.rev (E.symm i), ?_⟩
    rw [hasc, Fin.rev_rev]; rfl

lemma le_largest {R : Matrix I I ℂ} (hR : R.IsHermitian) (i : I) :
    hR.eigenvalues i ≤ largestEigenvalue R := by
  unfold largestEigenvalue; rw [range_asc hR]
  exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩

lemma largest_mem {R : Matrix I I ℂ} (hR : R.IsHermitian) : ∃ i, hR.eigenvalues i = largestEigenvalue R := by
  unfold largestEigenvalue; rw [range_asc hR]
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)

lemma psd_iff {R : Matrix I I ℂ} (hR : R.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • (1 : Matrix I I ℂ) - R).PosSemidef ↔ largestEigenvalue R ≤ c := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := largest_mem hR
    rw [← hi]
    set v := (hR.eigenvectorBasis i).ofLp
    have h1 := h.dotProduct_mulVec_nonneg v
    have hv : R *ᵥ v = hR.eigenvalues i • v := hR.mulVec_eigenvectorBasis i
    have hn : star v ⬝ᵥ v = 1 := by
      have := (hR.eigenvectorBasis).orthonormal.1 i
      rw [EuclideanSpace.norm_eq] at this
      have h2 : ∑ x, ‖(hR.eigenvectorBasis i).ofLp x‖ ^ 2 = 1 := by
        rw [Real.sqrt_eq_one] at this; exact this
      simp only [dotProduct, Pi.star_apply, v]
      have : ∑ x, ((‖(hR.eigenvectorBasis i).ofLp x‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast h2
      rw [← this]; refine Finset.sum_congr rfl fun x _ => ?_
      rw [RCLike.star_def, mul_comm, Complex.mul_conj']; push_cast; ring
    rw [sub_mulVec, smul_mulVec, one_mulVec, hv, dotProduct_sub, dotProduct_smul, dotProduct_smul, hn]
      at h1
    have := (Complex.nonneg_iff.1 h1).1
    simp at this; linarith
  · intro h
    have e : ((c : ℝ) : ℂ) • (1 : Matrix I I ℂ) - R = cfc (fun x => max (c - x) 0) R := by
      have : ((c : ℝ) : ℂ) • (1 : Matrix I I ℂ) - R = cfc (fun x : ℝ => c - x) R := by
        rw [cfc_sub _ _ R (X5SBM.fin _ _) (X5SBM.fin _ _), cfc_const c R, cfc_id' ℝ R hR.isSelfAdjoint,
          Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
      rw [this]
      refine cfc_congr fun x hx => ?_
      rw [hR.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [max_eq_left (by linarith [le_largest hR i])]
    rw [e]; exact cfc_psd hR _ fun x => le_max_right _ _

lemma largest_pos {R : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R) : 0 < largestEigenvalue R := by
  have h1 : ∑ i, hR.1.1.eigenvalues i = 1 := by rw [sum_eig, hR.2]; simp
  obtain ⟨i, hi⟩ : ∃ i, 0 < hR.1.1.eigenvalues i := by
    by_contra h; push_neg at h
    have : ∑ i, hR.1.1.eigenvalues i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  exact lt_of_lt_of_le hi (le_largest hR.1.1 i)

theorem maxRel_one {R : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R) :
    maxRelative R 1 = elog (largestEigenvalue R) := by
  have hp := largest_pos hR
  unfold elog; rw [if_pos hp]
  unfold maxRelative
  apply le_antisymm
  · refine sInf_le ⟨Real.logb 2 (largestEigenvalue R), rfl, ?_⟩
    rw [psd_iff hR.1.1, Real.rpow_logb (by norm_num) (by norm_num) hp]
  · refine le_sInf ?_
    rintro v ⟨L, rfl, hL⟩
    rw [psd_iff hR.1.1] at hL
    rw [EReal.coe_le_coe_iff, Real.logb_le_iff_le_rpow (by norm_num) hp]
    exact hL

theorem tr_supp_one {R : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R) :
    tr (support R * 1) = (R.rank : ℝ) := by
  unfold tr
  rw [Matrix.mul_one, X5MN.support_eq hR.1.1, tr_cfc hR.1.1, hR.1.1.rank_eq_card_non_zero_eigs]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [X5MN.ind]; split_ifs <;> simp_all

end X5SP
end X5mod_SP_Thm

section X5mod_EF_Thm
open Matrix Set
open scoped ComplexOrder

namespace X5EF
open X5DP X5RM X5SP
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (largestEigenvalue thresholdSet weakPositive)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cm (X : Matrix I I ℂ) (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (fin _ _) (fin _ _)).symm

noncomputable def kf : ℝ → ℝ := fun x => if x = 0 then 0 else Real.rpow x (-(1/2 : ℝ))
noncomputable def qf : ℝ → ℝ := fun x => if x = 0 then 0 else Real.rpow x (1/2 : ℝ)

section
variable {R S : Matrix I I ℂ} (hR : R.PosSemidef) (hS : S.PosSemidef)

include hS

lemma snn {x : ℝ} (hx : x ∈ spectrum ℝ S) : 0 ≤ x := by
  rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx; exact hS.eigenvalues_nonneg i

lemma KSK : cfc kf S * S * cfc kf S = cfc X5EP.ind S := by
  have : cfc kf S * S * cfc kf S = cfc kf S * cfc (fun x : ℝ => x) S * cfc kf S := by
    rw [cfc_id' ℝ S hS.1.isSelfAdjoint]
  rw [this, cm, cm]
  refine cfc_congr fun x hx => ?_
  have h0 := snn hS hx
  simp only [kf, X5EP.ind]
  split_ifs with h
  · simp
  · have hp : 0 < x := lt_of_le_of_ne h0 (Ne.symm h)
    simp only [Real.rpow_eq_pow]
    rw [mul_comm (x ^ (-(1/2:ℝ))) x, mul_assoc, ← Real.rpow_add hp,
      show (-(1/2:ℝ)) + -(1/2) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hp.ne']

lemma QK : cfc qf S * cfc kf S = cfc X5EP.ind S := by
  rw [cm]; refine cfc_congr fun x hx => ?_
  have h0 := snn hS hx
  simp only [kf, qf, X5EP.ind]
  split_ifs with h
  · simp
  · have hp : 0 < x := lt_of_le_of_ne h0 (Ne.symm h)
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hp]; norm_num

lemma KQ : cfc kf S * cfc qf S = cfc X5EP.ind S := by
  rw [cm, ← QK hS, cm]; refine cfc_congr fun x _ => ?_; ring

lemma QQ : cfc qf S * cfc qf S = S := by
  rw [cm]; conv_rhs => rw [← cfc_id' ℝ S hS.1.isSelfAdjoint]
  refine cfc_congr fun x hx => ?_
  have h0 := snn hS hx
  simp only [qf]
  split_ifs with h
  · simp [h]
  · have hp : 0 < x := lt_of_le_of_ne h0 (Ne.symm h)
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hp]; norm_num

lemma QP : cfc qf S * cfc X5EP.ind S = cfc qf S := by
  rw [cm]; refine cfc_congr fun x _ => ?_; simp only [qf, X5EP.ind]; split_ifs <;> simp

lemma PK : cfc X5EP.ind S * cfc kf S = cfc kf S := by
  rw [cm]; refine cfc_congr fun x _ => ?_; simp only [kf, X5EP.ind]; split_ifs <;> simp

lemma KP : cfc kf S * cfc X5EP.ind S = cfc kf S := by
  rw [cm]; refine cfc_congr fun x _ => ?_; simp only [kf, X5EP.ind]; split_ifs <;> simp

include hR in
lemma RPg (hsupp : SupportIncluded R S) : R * cfc X5EP.ind S = R := by
  have h0 : S * cfc (fun x => 1 - X5EP.ind x) S = 0 := by
    have : S * cfc (fun x => 1 - X5EP.ind x) S = cfc (fun x : ℝ => x) S * cfc (fun x => 1 - X5EP.ind x) S := by
      rw [cfc_id' ℝ S hS.1.isSelfAdjoint]
    rw [this, cm, ← cfc_const_zero ℝ S]
    refine cfc_congr fun x _ => ?_
    simp only [X5EP.ind]; split_ifs with h <;> simp [h]
  have k : R * cfc (fun x => 1 - X5EP.ind x) S = 0 := by
    ext i j
    have hc : S *ᵥ (fun k => cfc (fun x => 1 - X5EP.ind x) S k j) = 0 := by
      ext a; have := congrFun (congrFun h0 a) j; simpa [mulVec, dotProduct, mul_apply] using this
    have hc' : R *ᵥ (fun k => cfc (fun x => 1 - X5EP.ind x) S k j) = 0 := by
      have := hsupp (show (fun k => cfc (fun x => 1 - X5EP.ind x) S k j) ∈ LinearMap.ker S.mulVecLin by
        rw [LinearMap.mem_ker, mulVecLin_apply]; exact hc)
      rwa [LinearMap.mem_ker, mulVecLin_apply] at this
    have := congrFun hc' i
    simpa [mulVec, dotProduct, mul_apply] using this
  rw [cfc_sub _ _ S (fin _ _) (fin _ _), cfc_const_one ℝ S hS.1.isSelfAdjoint, Matrix.mul_sub,
    Matrix.mul_one, sub_eq_zero] at k
  exact k.symm

include hR in
lemma PRg (hsupp : SupportIncluded R S) : cfc X5EP.ind S * R = R := by
  have := congrArg conjTranspose (RPg hR hS hsupp)
  rwa [conjTranspose_mul, X5EP.PH, hR.1.eq] at this

lemma KH : (cfc kf S)ᴴ = cfc kf S := (cfc_predicate kf S : IsSelfAdjoint _)
lemma QH : (cfc qf S)ᴴ = cfc qf S := (cfc_predicate qf S : IsSelfAdjoint _)

end

section
variable {R S : Matrix I I ℂ} (hR : R.PosSemidef) (hRt : 0 < tr R) (hS : S.PosSemidef)
  (hsupp : SupportIncluded R S)
include hR hRt hS hsupp

lemma M_psd : (cfc kf S * R * cfc kf S).PosSemidef := by
  have := hR.conjTranspose_mul_mul_same (cfc kf S)
  rwa [KH hS] at this

lemma key (c : ℝ) : (((c : ℝ) : ℂ) • S - R).PosSemidef ↔
    largestEigenvalue (cfc kf S * R * cfc kf S) ≤ c := by
  set K := cfc kf S
  set Q := cfc qf S
  set P := cfc X5EP.ind S
  set M := K * R * K
  have hM := M_psd hR hRt hS hsupp
  have PK' : P * K = K := PK hS
  have KP' : K * P = K := KP hS
  have PM : P * M = M := by simp only [M, ← Matrix.mul_assoc, PK']
  constructor
  · intro h
    have htr := h.trace_nonneg
    have hc : 0 < c := by
      have h1 : 0 ≤ (((c : ℝ) : ℂ) • S - R).trace.re := (Complex.nonneg_iff.1 htr).1
      rw [Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h1
      have h2 : 0 ≤ S.trace.re := (Complex.nonneg_iff.1 hS.trace_nonneg).1
      unfold tr at hRt
      by_contra hc; push_neg at hc
      nlinarith
    obtain ⟨i, hi⟩ := largest_mem hM.1
    rcases le_or_gt (hM.1.eigenvalues i) 0 with h0 | h0
    · rw [← hi]; linarith
    rw [← hi]
    set v := (hM.1.eigenvectorBasis i).ofLp
    have hv : M *ᵥ v = hM.1.eigenvalues i • v := hM.1.mulVec_eigenvectorBasis i
    have hPv : P *ᵥ v = v := by
      have e : P *ᵥ (M *ᵥ v) = M *ᵥ v := by rw [mulVec_mulVec, PM]
      rw [hv, mulVec_smul] at e
      exact smul_right_injective _ (by exact_mod_cast h0.ne') e
    have hC := h.conjTranspose_mul_mul_same K
    rw [KH hS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, KSK hS] at hC
    have h1 := hC.dotProduct_mulVec_nonneg v
    have hn : star v ⬝ᵥ v = 1 := by
      have := (hM.1.eigenvectorBasis).orthonormal.1 i
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
      simp only [dotProduct, Pi.star_apply, v]
      have : ∑ x, ((‖(hM.1.eigenvectorBasis i).ofLp x‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast this
      rw [← this]; refine Finset.sum_congr rfl fun x _ => ?_
      exact (Complex.conj_mul' _).trans (by push_cast; ring)
    rw [sub_mulVec, smul_mulVec, hPv, show K * R * K = M from rfl, hv, dotProduct_sub, dotProduct_smul,
      dotProduct_smul, hn] at h1
    have := (Complex.nonneg_iff.1 h1).1
    simp at this; linarith
  · intro h
    have h1 : (((c : ℝ) : ℂ) • (1 : Matrix I I ℂ) - M).PosSemidef := (psd_iff hM.1 c).2 h
    have MP : M * P = M := by simp only [M, Matrix.mul_assoc, KP']
    have PH' : Pᴴ = P := X5EP.PH S
    have QH' : Qᴴ = Q := QH hS
    have PP' : P * P = P := X5EP.PP S
    have QP' : Q * P = Q := QP hS
    have QQ' : Q * Q = S := QQ hS
    have e : Q * M * Q = R := by
      have : Q * M * Q = (Q * K) * R * (K * Q) := by simp only [M, Matrix.mul_assoc]
      rw [this, show Q * K = P from QK hS, show K * Q = P from KQ hS, PRg hR hS hsupp, RPg hR hS hsupp]
    have e2 : Pᴴ * (((c : ℝ) : ℂ) • (1 : Matrix I I ℂ) - M) * P = ((c : ℝ) : ℂ) • P - M := by
      rw [PH', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, PP', PM, MP]
    have e3 : Qᴴ * (((c : ℝ) : ℂ) • P - M) * Q = ((c : ℝ) : ℂ) • S - R := by
      rw [QH', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, QP', QQ', e]
    have h2 := h1.conjTranspose_mul_mul_same P
    rw [e2] at h2
    have h3 := h2.conjTranspose_mul_mul_same Q
    rwa [e3] at h3

end

end X5EF
end X5mod_EF_Thm

section X5mod_RV_Base
open Matrix Set
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5RV
open X5RM X5EP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

section
variable {nu A : Matrix I I ℂ} (hnu : QAlgorithms.IsDensityMatrix nu) (hA : A.IsHermitian)
include hnu hA

/-- the compressed generator -/
noncomputable def Mg (nu A : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc X5EP.ind nu * A * cfc X5EP.ind nu + cfc Real.log nu

lemma PL : cfc X5EP.ind nu * cfc Real.log nu = cfc Real.log nu := by
  rw [cm]; refine cfc_congr fun x _ => ?_; simp only [X5EP.ind]; split_ifs with h <;> simp [h]
lemma LP : cfc Real.log nu * cfc X5EP.ind nu = cfc Real.log nu := by
  rw [cm]; refine cfc_congr fun x _ => ?_; simp only [X5EP.ind]; split_ifs with h <;> simp [h]

lemma MgH : (Mg nu A).IsHermitian := by
  unfold Mg IsHermitian
  have LH : (cfc Real.log nu)ᴴ = cfc Real.log nu := (cfc_predicate Real.log nu : IsSelfAdjoint _)
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, PH, hA.eq, LH, Matrix.mul_assoc]

lemma PMg : cfc X5EP.ind nu * Mg nu A = Mg nu A := by
  unfold Mg; rw [Matrix.mul_add, PL hnu hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, PP]

lemma MgP : Mg nu A * cfc X5EP.ind nu = Mg nu A := by
  unfold Mg; rw [Matrix.add_mul, LP hnu hA, Matrix.mul_assoc, PP]

lemma ex_c : ∃ c : ℝ, -c ∉ spectrum ℝ (Mg nu A) := by
  obtain ⟨x, hx⟩ := (Matrix.finite_real_spectrum (A := Mg nu A)).infinite_compl.nonempty
  exact ⟨-x, by simpa using hx⟩

section gibbs
variable {c : ℝ} (hc : -c ∉ spectrum ℝ (Mg nu A))
include hc

noncomputable def iN (c : ℝ) : ℝ → ℝ := fun x => if x = -c then 0 else 1
noncomputable def hN (c : ℝ) : ℝ → ℝ := fun x => if x = -c then 0 else Real.exp x

/-- the shifted generator -/
noncomputable def Ng (nu A : Matrix I I ℂ) (c : ℝ) : Matrix I I ℂ :=
  Mg nu A - ((c : ℝ) : ℂ) • (1 - cfc X5EP.ind nu)

lemma cfcN (f : ℝ → ℝ) : cfc f (Ng nu A c) = cfc f (Mg nu A) * cfc X5EP.ind nu +
    ((f (-c) : ℝ) : ℂ) • (1 - cfc X5EP.ind nu) :=
  cfc_N (PMg hnu hA) (MgP hnu hA) (PP nu) (MgH hnu hA) (PH nu) c f

lemma NgH : (Ng nu A c).IsHermitian := by
  unfold Ng; refine (MgH hnu hA).sub ?_
  unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, PH]; simp

lemma P_eq : cfc (iN c) (Ng nu A c) = cfc X5EP.ind nu := by
  rw [cfcN hnu hA hc]
  have : cfc (iN c) (Mg nu A) = 1 := by
    rw [← cfc_const_one ℝ (Mg nu A) (MgH hnu hA).isSelfAdjoint]
    refine cfc_congr fun x hx => ?_
    have : x ≠ -c := fun h => hc (h ▸ hx)
    simp [iN, this]
  rw [this, Matrix.one_mul]; simp [iN]

lemma T_eq : cfc (hN c) (Ng nu A c) = cfc Real.exp (Mg nu A) * cfc X5EP.ind nu := by
  rw [cfcN hnu hA hc]
  have : cfc (hN c) (Mg nu A) = cfc Real.exp (Mg nu A) := by
    refine cfc_congr fun x hx => ?_
    have : x ≠ -c := fun h => hc (h ▸ hx)
    simp [hN, this]
  rw [this]; simp [hN]

lemma comp_eq : compressedExp A nu = cfc (hN c) (Ng nu A c) := by
  unfold compressedExp
  rw [X5MN.support_eq hnu.1.1, show logMat nu = cfc Real.log nu from rfl,
    show cfc X5MN.ind nu = cfc X5EP.ind nu from rfl,
    show cfc X5EP.ind nu * A * cfc X5EP.ind nu + cfc Real.log nu = Mg nu A from rfl,
    ← CFC.real_exp_eq_normedSpace_exp (MgH hnu hA).isSelfAdjoint, Matrix.mul_assoc, ← T_eq hnu hA hc,
    ← P_eq hnu hA hc, cm]
  refine cfc_congr fun x _ => ?_
  simp only [iN, hN]; split_ifs <;> simp

noncomputable def Zg (nu A : Matrix I I ℂ) (c : ℝ) : ℝ := (cfc (hN c) (Ng nu A c)).trace.re

lemma Z_pos : 0 < Zg nu A c := by
  have hN1 := NgH hnu hA hc
  unfold Zg; rw [tr_cfc hN1]
  have nn : ∀ i, 0 ≤ hN c (hN1.eigenvalues i) := fun i => by
    unfold hN; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  by_contra hle; push_neg at hle
  have h0 : ∀ i, hN c (hN1.eigenvalues i) = 0 := fun i =>
    le_antisymm (by
      have := Finset.single_le_sum (fun j _ => nn j) (Finset.mem_univ i)
      linarith) (nn i)
  have hall : ∀ i, hN1.eigenvalues i = -c := by
    intro i; have := h0 i; unfold hN at this
    split_ifs at this with h
    · exact h
    · exact absurd this (Real.exp_pos _).ne'
  have hP0 : cfc X5EP.ind nu = 0 := by
    rw [← P_eq hnu hA hc, ← cfc_const_zero ℝ (Ng nu A c)]
    refine cfc_congr fun x hx => ?_
    rw [hN1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [iN, hall i]
  have := XP hnu.1.1
  rw [hP0, Matrix.mul_zero] at this
  have h2 := hnu.2; rw [← this, Matrix.trace_zero] at h2
  exact zero_ne_one h2

noncomputable def σg (nu A : Matrix I I ℂ) (c : ℝ) : Matrix I I ℂ :=
  cfc (fun x => hN c x / Zg nu A c) (Ng nu A c)

lemma σ_eq : σg nu A c = (Zg nu A c)⁻¹ • cfc (hN c) (Ng nu A c) := by
  unfold σg
  rw [show (fun x => hN c x / Zg nu A c) = fun x => (Zg nu A c)⁻¹ * hN c x by funext x; ring]
  exact cfc_const_mul _ _ _ (fin _ _)

lemma σ_dens : QAlgorithms.IsDensityMatrix (σg nu A c) := by
  have hN1 := NgH hnu hA hc
  have hZ := Z_pos hnu hA hc
  have nn : ∀ x, 0 ≤ hN c x / Zg nu A c := fun x => div_nonneg (by
    unfold hN; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le) hZ.le
  refine ⟨cfc_psd hN1 _ nn, ?_⟩
  have hre : (σg nu A c).trace.re = 1 := by
    rw [σ_eq hnu hA hc, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
    unfold Zg at hZ ⊢; field_simp
  have him : (σg nu A c).trace.im = 0 :=
    ((Complex.nonneg_iff.1 (cfc_psd hN1 _ nn).trace_nonneg).2).symm
  exact Complex.ext hre him

lemma log_σ : cfc Real.log (σg nu A c) = Mg nu A - (Real.log (Zg nu A c) : ℂ) • cfc X5EP.ind nu := by
  have hZ := Z_pos hnu hA hc
  unfold σg
  rw [← cfc_comp' Real.log _ _ ((Set.toFinite _).continuousOn _) (fin _ _) (NgH hnu hA hc).isSelfAdjoint,
    cfcN hnu hA hc]
  have : cfc (fun x => Real.log (hN c x / Zg nu A c)) (Mg nu A) =
      Mg nu A - (Real.log (Zg nu A c) : ℂ) • 1 := by
    rw [show (Mg nu A - (Real.log (Zg nu A c) : ℂ) • 1) =
        cfc (fun x : ℝ => x - Real.log (Zg nu A c)) (Mg nu A) by
      rw [cfc_sub _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ _ (MgH hnu hA).isSelfAdjoint, cfc_const _ _ (MgH hnu hA).isSelfAdjoint,
        Algebra.algebraMap_eq_smul_one, Complex.coe_smul]]
    refine cfc_congr fun x hx => ?_
    have : x ≠ -c := fun h => hc (h ▸ hx)
    simp only [hN, if_neg this]
    rw [Real.log_div (Real.exp_pos x).ne' hZ.ne', Real.log_exp]
  rw [this]
  have h0 : hN c (-c) = 0 := by simp [hN]
  rw [h0, zero_div, Real.log_zero, Complex.ofReal_zero, zero_smul, add_zero]
  rw [Matrix.sub_mul, MgP hnu hA, Matrix.smul_mul, Matrix.one_mul]

lemma σP : σg nu A c * cfc X5EP.ind nu = σg nu A c := by
  unfold σg; rw [← P_eq hnu hA hc, cm]
  refine cfc_congr fun x _ => ?_; simp only [iN, hN]; split_ifs <;> simp

lemma ker_σ : LinearMap.ker (σg nu A c).mulVecLin ≤ LinearMap.ker nu.mulVecLin := by
  have hZ := Z_pos hnu hA hc
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have e : cfc (fun x => if x = -c then 0 else Zg nu A c / Real.exp x) (Ng nu A c) * σg nu A c =
      cfc X5EP.ind nu := by
    unfold σg; rw [← P_eq hnu hA hc, cm]
    refine cfc_congr fun x _ => ?_; simp only [iN, hN]; split_ifs
    · simp
    · field_simp
  have hPv : cfc X5EP.ind nu *ᵥ v = 0 := by rw [← e, ← mulVec_mulVec, hv, mulVec_zero]
  rw [← XP hnu.1.1, ← mulVec_mulVec, hPv, mulVec_zero]

lemma ker_ν : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker (σg nu A c).mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have hPv : cfc X5EP.ind nu *ᵥ v = 0 := by rw [← pinvX hnu.1.1, ← mulVec_mulVec, hv, mulVec_zero]
  rw [← σP hnu hA hc, ← mulVec_mulVec, hPv, mulVec_zero]

/-- the key identity -/
lemma Dr_id {rho : Matrix I I ℂ} (hr : QAlgorithms.IsDensityMatrix rho)
    (hs : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    Dr rho (σg nu A c) = Dr rho nu - (A * rho).trace.re + Real.log (Zg nu A c) := by
  have RP := X5EF.RPg hr.1 hnu.1 hs
  have PR := X5EF.PRg hr.1 hnu.1 hs
  rw [Dr_split, Dr_split, log_σ hnu hA hc]
  unfold Mg
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, RP, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, hr.2]
  have e : (rho * (cfc X5EP.ind nu * A * cfc X5EP.ind nu)).trace = (A * rho).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, RP, Matrix.trace_mul_comm, ← Matrix.mul_assoc, PR,
      Matrix.trace_mul_comm]
  rw [e]
  simp only [Complex.sub_re, Complex.add_re, smul_eq_mul, mul_one, Complex.ofReal_re]
  ring

end gibbs

end

end X5RV
end X5mod_RV_Base

section X5mod_RV_P2
open Matrix Set
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5RV
open X5RM X5EP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

section
variable {nu A : Matrix I I ℂ} (hnu : QAlgorithms.IsDensityMatrix nu) (hA : A.IsHermitian)
include hnu hA

lemma tr_comp {c : ℝ} (hc : -c ∉ spectrum ℝ (Mg nu A)) :
    (compressedExp A nu).trace = ((Zg nu A c : ℝ) : ℂ) := by
  rw [comp_eq hnu hA hc]
  have hN1 := NgH hnu hA hc
  have nn : ∀ x, 0 ≤ hN c x := fun x => by
    unfold hN; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  refine Complex.ext rfl ?_
  have := ((Complex.nonneg_iff.1 (cfc_psd hN1 _ nn).trace_nonneg).2).symm
  simpa using this

lemma rmax_eq {c : ℝ} (hc : -c ∉ spectrum ℝ (Mg nu A)) :
    ((compressedExp A nu).trace)⁻¹ • compressedExp A nu = σg nu A c := by
  rw [tr_comp hnu hA hc, σ_eq hnu hA hc, comp_eq hnu hA hc, ← Complex.ofReal_inv, Complex.coe_smul]

theorem part2 : QAlgorithms.IsDensityMatrix (((compressedExp A nu).trace)⁻¹ • compressedExp A nu) ∧
    (∀ rho : Matrix I I ℂ, QAlgorithms.IsDensityMatrix rho →
      signedRelativeEntropy rho nu + (ev rho A : EReal) ≤
        (Real.log ((compressedExp A nu).trace.re) : EReal) ∧
      (signedRelativeEntropy rho nu + (ev rho A : EReal) =
        (Real.log ((compressedExp A nu).trace.re) : EReal) ↔
          rho = ((compressedExp A nu).trace)⁻¹ • compressedExp A nu)) := by
  obtain ⟨c, hc⟩ := ex_c hnu hA
  rw [rmax_eq hnu hA hc, tr_comp hnu hA hc, Complex.ofReal_re]
  refine ⟨σ_dens hnu hA hc, fun rho hr => ?_⟩
  have hev : ev rho A = (A * rho).trace.re := rfl
  by_cases hs : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin
  · rw [sRE_pos hs, hev, ← EReal.coe_add]
    have hid := Dr_id hnu hA hc hr hs
    have hk := klein hr (σ_dens hnu hA hc) ((ker_σ hnu hA hc).trans hs)
    refine ⟨EReal.coe_le_coe_iff.2 (by linarith), ?_⟩
    rw [EReal.coe_eq_coe_iff]
    constructor
    · intro h
      exact X5SK.klein_eq hr (σ_dens hnu hA hc) ((ker_σ hnu hA hc).trans hs) (by linarith)
    · intro h
      have h0 := Dr_self hr.1.1
      have e := hid
      rw [← h] at e
      linarith
  · rw [sRE_neg hs, EReal.bot_add]
    refine ⟨bot_le, ?_⟩
    constructor
    · intro h; exact absurd h.symm (EReal.coe_ne_bot _)
    · intro h
      exact absurd (h ▸ ker_ν hnu hA hc) hs

end

end X5RV
end X5mod_RV_P2

section X5mod_RV_P1
open Matrix Set Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5RV
open X5RM X5EP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma killg {X Y M : Matrix I I ℂ} (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin)
    (h : Y * M = 0) : X * M = 0 := by
  ext i j
  have hc : Y *ᵥ (fun k => M k j) = 0 := by
    ext a; have := congrFun (congrFun h a) j; simpa [mulVec, dotProduct, mul_apply] using this
  have hc' : X *ᵥ (fun k => M k j) = 0 := by
    have := hs (show (fun k => M k j) ∈ LinearMap.ker Y.mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply]; exact hc)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have := congrFun hc' i
  simpa [mulVec, dotProduct, mul_apply] using this

lemma half {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    cfc X5EP.ind X * cfc X5EP.ind Y = cfc X5EP.ind X := by
  have h1 : Y * (1 - cfc X5EP.ind Y) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, XP hY, sub_self]
  have h2 := killg hs h1
  have h3 : cfc X5EP.ind X * (1 - cfc X5EP.ind Y) = 0 := by
    rw [← pinvX hX, Matrix.mul_assoc, h2, Matrix.mul_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h3
  exact h3.symm

lemma proj_eq {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h1 : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin)
    (h2 : LinearMap.ker X.mulVecLin ≤ LinearMap.ker Y.mulVecLin) :
    cfc X5EP.ind X = cfc X5EP.ind Y := by
  have a := half hX hY h1
  have b := half hY hX h2
  have := congrArg conjTranspose a
  rw [conjTranspose_mul, PH, PH] at this
  calc cfc X5EP.ind X = cfc X5EP.ind Y * cfc X5EP.ind X := this.symm
    _ = cfc X5EP.ind Y := b

section
variable {nu A : Matrix I I ℂ} (hnu : QAlgorithms.IsDensityMatrix nu) (hA : A.IsHermitian)
include hnu hA

/-- the variational value in terms of relative entropies -/
lemma F_eq {rho : Matrix I I ℂ} (hr : QAlgorithms.IsDensityMatrix rho)
    (hs : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    Real.log ((compressedExp A nu).trace.re) - ev rho A =
      Dr rho (((compressedExp A nu).trace)⁻¹ • compressedExp A nu) - Dr rho nu := by
  obtain ⟨c, hc⟩ := ex_c hnu hA
  rw [rmax_eq hnu hA hc, tr_comp hnu hA hc, Complex.ofReal_re, Dr_id hnu hA hc hr hs]
  unfold ev QAlgorithms.effectProb; ring

/-- if the compressed generator is log tau + c P, the maximiser is tau -/
lemma rmax_of {tau : Matrix I I ℂ} (ht : QAlgorithms.IsDensityMatrix tau)
    (hsupp : support tau = support nu) (c : ℝ)
    (hc : support nu * A * support nu = logMat tau - logMat nu + (c : ℂ) • support nu) :
    ((compressedExp A nu).trace)⁻¹ • compressedExp A nu = tau := by
  have hP : support nu = cfc X5EP.ind tau := by rw [← hsupp, X5MN.support_eq ht.1.1]; rfl
  have hM : support nu * A * support nu + logMat nu = cfc (fun x => Real.log x + c * X5EP.ind x) tau := by
    rw [hc, show logMat tau - logMat nu + (c : ℂ) • support nu + logMat nu =
      logMat tau + (c : ℂ) • support nu by abel, hP, cfc_add _ _ _ (fin _ _) (fin _ _), cfc_const_mul _ _ _ (fin _ _),
      Complex.coe_smul]; rfl
  have hMH : (cfc (fun x => Real.log x + c * X5EP.ind x) tau).IsHermitian :=
    (cfc_predicate _ tau : IsSelfAdjoint _)
  have hT : compressedExp A nu = (Real.exp c : ℂ) • tau := by
    unfold compressedExp
    rw [hM, ← CFC.real_exp_eq_normedSpace_exp hMH.isSelfAdjoint,
      ← cfc_comp' Real.exp _ tau Real.continuous_exp.continuousOn (fin _ _) ht.1.1.isSelfAdjoint,
      hP, cm, cm]
    rw [show (Real.exp c : ℂ) • tau = cfc (fun x : ℝ => Real.exp c * x) tau by
      rw [cfc_const_mul _ _ _ (fin _ _), cfc_id' ℝ tau ht.1.1.isSelfAdjoint, Complex.coe_smul]]
    refine cfc_congr fun x hx => ?_
    have h0 : 0 ≤ x := by
      rw [ht.1.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx; exact ht.1.eigenvalues_nonneg i
    simp only [X5EP.ind]
    split_ifs with h
    · simp [h]
    · have hp : 0 < x := lt_of_le_of_ne h0 (Ne.symm h)
      rw [mul_one, mul_one, one_mul, Real.exp_add, Real.exp_log hp]; ring
  rw [hT, Matrix.trace_smul, ht.2, smul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀
    (by exact_mod_cast (Real.exp_pos c).ne'), one_smul]

end

end X5RV
end X5mod_RV_P1

section X5mod_RV_P1b
open Matrix Set Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5RV
open X5RM X5EP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def Fv (rho nu A : Matrix I I ℂ) : ℝ :=
  Real.log ((compressedExp A nu).trace.re) - ev rho A

section
variable {rho nu : Matrix I I ℂ} (hr : QAlgorithms.IsDensityMatrix rho)
  (hnu : QAlgorithms.IsDensityMatrix nu)
include hr hnu

lemma le_F {A : Matrix I I ℂ} (hA : A.IsHermitian) : signedRelativeEntropy rho nu ≤ (Fv rho nu A : EReal) := by
  have h := ((part2 hnu hA).2 rho hr).1
  by_cases hs : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin
  · rw [sRE_pos hs] at h ⊢
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]; unfold Fv; linarith
  · rw [sRE_neg hs]; exact bot_le

lemma supp_of (h : support rho = support nu) :
    LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have hPv : cfc X5EP.ind nu *ᵥ v = 0 := by rw [← pinvX hnu.1.1, ← mulVec_mulVec, hv, mulVec_zero]
  have e : cfc X5EP.ind rho = cfc X5EP.ind nu := by
    have := h; rw [X5MN.support_eq hr.1.1, X5MN.support_eq hnu.1.1] at this; exact this
  rw [← XP hr.1.1, e, ← mulVec_mulVec, hPv, mulVec_zero]

lemma eq_iff (h : support rho = support nu) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    signedRelativeEntropy rho nu = (Fv rho nu A : EReal) ↔
      ∃ c : ℝ, support nu * A * support nu = logMat rho - logMat nu + (c : ℂ) • support nu := by
  have hs := supp_of hr hnu h
  obtain ⟨c0, hc0⟩ := ex_c hnu hA
  have hF := F_eq hnu hA hr hs
  rw [rmax_eq hnu hA hc0] at hF
  have hσ := σ_dens hnu hA hc0
  have hk : LinearMap.ker (σg nu A c0).mulVecLin ≤ LinearMap.ker rho.mulVecLin := (ker_σ hnu hA hc0).trans hs
  rw [sRE_pos hs, EReal.coe_eq_coe_iff]
  unfold Fv; rw [hF]
  constructor
  · intro he
    have h0 : Dr rho (σg nu A c0) = 0 := by linarith
    have hρ := X5SK.klein_eq hr hσ hk h0
    refine ⟨Real.log (Zg nu A c0), ?_⟩
    have hl := log_σ hnu hA hc0
    rw [← hρ] at hl
    unfold Mg at hl
    rw [X5MN.support_eq hnu.1.1, show logMat rho = cfc Real.log rho from rfl,
      show logMat nu = cfc Real.log nu from rfl, show cfc X5MN.ind nu = cfc X5EP.ind nu from rfl, hl]
    abel
  · rintro ⟨c, hc⟩
    have hm := rmax_of hnu hA hr h c hc
    rw [rmax_eq hnu hA hc0] at hm
    rw [hm, Dr_self hr.1.1]; ring

lemma attain (h : support rho = support nu) :
    ∃ A : Matrix I I ℂ, A.IsHermitian ∧ signedRelativeEntropy rho nu = (Fv rho nu A : EReal) := by
  have hLH : ∀ X : Matrix I I ℂ, (logMat X).IsHermitian := fun X => (cfc_predicate Real.log X : IsSelfAdjoint _)
  have hAH : (logMat rho - logMat nu).IsHermitian := (hLH rho).sub (hLH nu)
  refine ⟨logMat rho - logMat nu, hAH, (eq_iff hr hnu h hAH).2 ⟨0, ?_⟩⟩
  have hPr : support nu = cfc X5EP.ind rho := by rw [← h, X5MN.support_eq hr.1.1]; rfl
  have hPn : support nu = cfc X5EP.ind nu := by rw [X5MN.support_eq hnu.1.1]; rfl
  rw [Matrix.mul_sub, Matrix.sub_mul, Complex.ofReal_zero, zero_smul, add_zero]
  congr 1
  · rw [hPr, show logMat rho = cfc Real.log rho from rfl, PL hr hAH, LP hr hAH]
  · rw [hPn, show logMat nu = cfc Real.log nu from rfl, PL hnu hAH, LP hnu hAH]

end

end X5RV
end X5mod_RV_P1b

section X5mod_RV_P1c
open Matrix Set Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace X5RV
open X5RM X5EP
open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

section
variable {rho nu : Matrix I I ℂ} (hr : QAlgorithms.IsDensityMatrix rho)
  (hnu : QAlgorithms.IsDensityMatrix nu)
include hr hnu

lemma F_tau (hs : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin)
    {tau : Matrix I I ℂ} (ht : QAlgorithms.IsDensityMatrix tau) (h : support tau = support nu) :
    ∃ A : Matrix I I ℂ, A.IsHermitian ∧ Fv rho nu A = Dr rho tau - Dr rho nu := by
  have hLH : ∀ X : Matrix I I ℂ, (logMat X).IsHermitian := fun X => (cfc_predicate Real.log X : IsSelfAdjoint _)
  have hAH : (logMat tau - logMat nu).IsHermitian := (hLH tau).sub (hLH nu)
  refine ⟨logMat tau - logMat nu, hAH, ?_⟩
  have hc : support nu * (logMat tau - logMat nu) * support nu =
      logMat tau - logMat nu + ((0 : ℝ) : ℂ) • support nu := by
    have hPr : support nu = cfc X5EP.ind tau := by rw [← h, X5MN.support_eq ht.1.1]; rfl
    have hPn : support nu = cfc X5EP.ind nu := by rw [X5MN.support_eq hnu.1.1]; rfl
    rw [Matrix.mul_sub, Matrix.sub_mul, Complex.ofReal_zero, zero_smul, add_zero]
    congr 1
    · rw [hPr, show logMat tau = cfc Real.log tau from rfl, PL ht hAH, LP ht hAH]
    · rw [hPn, show logMat nu = cfc Real.log nu from rfl, PL hnu hAH, LP hnu hAH]
  have hm := rmax_of hnu hAH ht h 0 hc
  unfold Fv
  rw [F_eq hnu hAH hr hs, hm]

theorem inf_eq : signedRelativeEntropy rho nu =
    sInf {v | ∃ A : Matrix I I ℂ, A.IsHermitian ∧ v = (Fv rho nu A : EReal)} := by
  apply le_antisymm
  · refine le_sInf ?_
    rintro v ⟨A, hA, rfl⟩
    exact le_F hr hnu hA
  by_cases hs : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker rho.mulVecLin
  · rw [sRE_pos hs]
    set D := Dr rho nu
    have key : ∀ ε ∈ Ioo (0 : ℝ) 1,
        sInf {v | ∃ A : Matrix I I ℂ, A.IsHermitian ∧ v = (Fv rho nu A : EReal)} ≤ (((ε - 1) * D : ℝ) : EReal) := by
      intro ε hε
      set tau := mix ε nu rho
      have ht : QAlgorithms.IsDensityMatrix tau := mix_dens ⟨hε.1.le, hε.2.le⟩ hnu hr
      have k1 : LinearMap.ker tau.mulVecLin ≤ LinearMap.ker nu.mulVecLin := (ker_mix hε hnu.1 hr.1).1
      have k2 : LinearMap.ker nu.mulVecLin ≤ LinearMap.ker tau.mulVecLin := by
        intro v hv
        have hv' := hs hv
        rw [LinearMap.mem_ker, mulVecLin_apply] at hv hv' ⊢
        simp [tau, mix, add_mulVec, smul_mulVec, hv, hv']
      have hsupp : support tau = support nu := by
        rw [X5MN.support_eq ht.1.1, X5MN.support_eq hnu.1.1]
        exact proj_eq ht.1.1 hnu.1.1 k2 k1
      obtain ⟨A, hA, hF⟩ := F_tau hr hnu hs ht hsupp
      have hj := rjoint rho rho nu rho hr hr hnu hr ε ⟨hε.1.le, hε.2.le⟩
      have hrr : (ε : ℂ) • rho + ((1 - ε : ℝ) : ℂ) • rho = rho := by
        rw [← add_smul]; push_cast; simp
      rw [hrr, show (ε : ℂ) • nu + ((1 - ε : ℝ) : ℂ) • rho = tau from rfl, sRE_pos hs, sRE_pos (le_refl _),
        Dr_self hr.1.1, sRE_pos (k1.trans hs)] at hj
      change (ε : EReal) * ((-D : ℝ) : EReal) + ((1 - ε : ℝ) : EReal) * ((-0 : ℝ) : EReal) ≤
        ((-Dr rho tau : ℝ) : EReal) at hj
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hj
      refine sInf_le_of_le ⟨A, hA, rfl⟩ ?_
      rw [EReal.coe_le_coe_iff, hF]; nlinarith
    have lim : Tendsto (fun ε : ℝ => (((ε - 1) * D : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ((-D : ℝ) : EReal)) := by
      have : Tendsto (fun ε : ℝ => (ε - 1) * D) (𝓝[>] 0) (𝓝 (-D)) := by
        have h := ((continuous_id.sub continuous_const).mul continuous_const).tendsto (0 : ℝ)
          (f := fun ε : ℝ => (ε - 1) * D)
        simp only [zero_sub, neg_one_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact (continuous_coe_real_ereal.tendsto _).comp this
    refine ge_of_tendsto lim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact key ε hε
  · rw [sRE_neg hs]
    apply le_of_eq
    rw [EReal.eq_bot_iff_forall_lt]
    intro r
    set Q := 1 - cfc X5EP.ind nu
    have hQH : Qᴴ = Q := by rw [conjTranspose_sub, conjTranspose_one, PH]
    have hQQ : Q * Q = Q := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, PP, sub_self, sub_zero]
    set q := (Q * rho).trace.re
    have eQ : (Q * rho).trace = (rho * Q).trace := Matrix.trace_mul_comm _ _
    have hq0 : 0 ≤ q := by
      have := (hr.1.conjTranspose_mul_mul_same Q).trace_nonneg
      rw [hQH, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hQQ] at this
      rw [← eQ] at this; exact (Complex.nonneg_iff.1 this).1
    have hqi : (Q * rho).trace.im = 0 := by
      have := (hr.1.conjTranspose_mul_mul_same Q).trace_nonneg
      rw [hQH, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hQQ] at this
      rw [← eQ] at this; exact ((Complex.nonneg_iff.1 this).2).symm
    have hq : 0 < q := by
      refine lt_of_le_of_ne hq0 fun h0 => hs ?_
      have ht0 : (rho * Q).trace = 0 := by
        rw [Matrix.trace_mul_comm]; exact Complex.ext h0.symm hqi
      have hz := proj_zero hr.1 hQH hQQ ht0
      intro v hv
      rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
      have hPv : cfc X5EP.ind nu *ᵥ v = 0 := by rw [← pinvX hnu.1.1, ← mulVec_mulVec, hv, mulVec_zero]
      have : rho = rho * cfc X5EP.ind nu := by
        have := hz; rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this; exact this
      rw [this, ← mulVec_mulVec, hPv, mulVec_zero]
    set K0 := Real.log ((compressedExp 0 nu).trace.re)
    set t := (K0 - r + 1) / q
    have hAH : (((t : ℝ) : ℂ) • Q).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_smul, hQH]; simp
    have hcomp : compressedExp (((t : ℝ) : ℂ) • Q) nu = compressedExp 0 nu := by
      unfold compressedExp
      rw [X5MN.support_eq hnu.1.1, show cfc X5MN.ind nu = cfc X5EP.ind nu from rfl]
      have : cfc X5EP.ind nu * (((t : ℝ) : ℂ) • Q) * cfc X5EP.ind nu = cfc X5EP.ind nu * 0 * cfc X5EP.ind nu := by
        rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_smul, Matrix.smul_mul]
        have : cfc X5EP.ind nu * Q = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one]; exact sub_eq_zero.2 (PP nu).symm
        rw [this, Matrix.zero_mul, smul_zero]
      rw [this]
    have hF : Fv rho nu (((t : ℝ) : ℂ) • Q) = r - 1 := by
      unfold Fv ev QAlgorithms.effectProb
      rw [hcomp, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      change K0 - t * q = r - 1
      unfold t; field_simp; ring
    calc sInf {v | ∃ A : Matrix I I ℂ, A.IsHermitian ∧ v = (Fv rho nu A : EReal)}
        ≤ (Fv rho nu (((t : ℝ) : ℂ) • Q) : EReal) := sInf_le ⟨_, hAH, rfl⟩
      _ < (r : EReal) := by rw [hF, EReal.coe_lt_coe_iff]; linarith

end

end X5RV
end X5mod_RV_P1c

section X5mod_RV_T

end X5mod_RV_T

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] :
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      signedRelativeEntropy rho nu = sInf {v | ∃ A : Mat I, A.IsHermitian ∧
        v = ((Real.log ((compressedExp A nu).trace.re) - ev rho A : ℝ) : EReal)} ∧
      (support rho = support nu →
        (∃ A : Mat I, A.IsHermitian ∧ signedRelativeEntropy rho nu =
          ((Real.log ((compressedExp A nu).trace.re) - ev rho A : ℝ) : EReal)) ∧
        (∀ A : Mat I, A.IsHermitian →
          (signedRelativeEntropy rho nu = ((Real.log ((compressedExp A nu).trace.re) - ev rho A : ℝ) : EReal) ↔
            ∃ c : ℝ, support nu * A * support nu =
              logMat rho - logMat nu + (c : ℂ) • support nu)))) ∧
    (∀ A nu : Mat I, A.IsHermitian → QAlgorithms.IsDensityMatrix nu →
      let rhoMax := ((compressedExp A nu).trace)⁻¹ • compressedExp A nu
      QAlgorithms.IsDensityMatrix rhoMax ∧
      (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
        signedRelativeEntropy rho nu + (ev rho A : EReal) ≤ (Real.log ((compressedExp A nu).trace.re) : EReal) ∧
        (signedRelativeEntropy rho nu + (ev rho A : EReal) =
          (Real.log ((compressedExp A nu).trace.re) : EReal) ↔ rho = rhoMax))) :=
  ⟨fun rho nu hr hnu => ⟨X5RV.inf_eq hr hnu, fun h => ⟨X5RV.attain hr hnu h,
      fun A hA => X5RV.eq_iff hr hnu h hA⟩⟩,
   fun A nu hA hnu => X5RV.part2 hnu hA⟩

end
