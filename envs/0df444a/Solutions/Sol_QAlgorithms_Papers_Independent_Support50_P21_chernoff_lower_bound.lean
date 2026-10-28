-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.chernoff_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:53:23.954278+00:00
-- url     : https://prove2.me/submissions/28e17b4c-a836-48d2-99ee-d5abdb91bc43

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

section X5mod_CH_Thm
open Matrix Set Filter Topology
open scoped ComplexOrder

namespace X5CH
open X5DP X5RM
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog)
open QAlgorithms.Papers.Independent.Support50.P21 (dMin chernoff chernoffCoefficient)

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def pw (s x : ℝ) : ℝ := if x = 0 then 0 else Real.rpow x s

lemma q_sum {R S : Matrix I I ℂ} (hR : R.IsHermitian) (hS : S.IsHermitian) (s : ℝ) :
    chernoffCoefficient R S s = ∑ i, ∑ j, pw s (hR.eigenvalues i) * pw (1 - s) (hS.eigenvalues j) *
      X5OL.w hR hS i j := by
  unfold chernoffCoefficient tr supportPower
  rw [X5OL.tr_cfc_cfc hR hS]
  simp [Complex.re_sum, pw]

lemma pw_cont {x : ℝ} (hx : 0 ≤ x) : Continuous fun s => pw s x := by
  unfold pw
  by_cases h : x = 0
  · simp only [h, if_true]; exact continuous_const
  · simp only [h, if_false]
    exact continuous_const.rpow continuous_id fun _ => Or.inl h

lemma pw_nonneg (s : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pw s x := by
  unfold pw; split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg hx s

section
variable {R S : Matrix I I ℂ} (hR : QAlgorithms.IsDensityMatrix R) (hS : QAlgorithms.IsDensityMatrix S)
include hR hS

lemma q_cont : Continuous fun s => chernoffCoefficient R S s := by
  have e : (fun s => chernoffCoefficient R S s) = fun s => ∑ i, ∑ j, pw s (hR.1.1.eigenvalues i) *
      pw (1 - s) (hS.1.1.eigenvalues j) * X5OL.w hR.1.1 hS.1.1 i j := by
    funext s; exact q_sum hR.1.1 hS.1.1 s
  rw [e]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  refine ((pw_cont (hR.1.eigenvalues_nonneg i)).mul ?_).mul continuous_const
  exact (pw_cont (hS.1.eigenvalues_nonneg j)).comp (continuous_const.sub continuous_id)

lemma q_nonneg (s : ℝ) : 0 ≤ chernoffCoefficient R S s := by
  rw [q_sum hR.1.1 hS.1.1]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (pw_nonneg s (hR.1.eigenvalues_nonneg i)) (pw_nonneg _ (hS.1.eigenvalues_nonneg j)))
      (X5OL.w_nonneg _ _ _ _)

lemma q_zero : chernoffCoefficient R S 0 = tr (support R * S) := by
  unfold chernoffCoefficient tr
  have e1 : supportPower S (1 - 0) = S := by
    unfold supportPower
    conv_rhs => rw [← cfc_id' ℝ S hS.1.1.isSelfAdjoint]
    refine cfc_congr fun x _ => ?_
    by_cases h : x = 0
    · simp [h]
    · simp [h]
  have e0 : supportPower R 0 = support R := by
    rw [X5MN.support_eq hR.1.1]
    unfold supportPower
    refine cfc_congr fun x _ => ?_
    by_cases h : x = 0
    · simp [h, X5MN.ind]
    · simp [h, X5MN.ind]
  rw [e1, e0]

theorem main : dMin R S ≤ chernoff R S ∧
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      IsLeast (chernoffCoefficient R S '' Set.Icc (0 : ℝ) 1) (chernoffCoefficient R S s) := by
  constructor
  · unfold dMin chernoff
    refine EReal.neg_le_neg_iff.2 (X5MN.elog_mono ?_)
    rw [← q_zero hR hS]
    refine csInf_le ⟨0, ?_⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    rintro _ ⟨t, _, rfl⟩; exact q_nonneg hR hS t
  · obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
      (q_cont hR hS).continuousOn
    refine ⟨s, hs, ⟨s, hs, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hmin ht

end

end X5CH
end X5mod_CH_Thm

section X5mod_CH_T

end X5mod_CH_T

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P21
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

section Statements

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Nonempty I] [Nonempty J]

theorem solution (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    dMin rho sigma ≤ chernoff rho sigma ∧
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      IsLeast (chernoffCoefficient rho sigma '' Set.Icc (0 : ℝ) 1)
        (chernoffCoefficient rho sigma s) :=
  X5CH.main hrho hsigma

end Statements

end
