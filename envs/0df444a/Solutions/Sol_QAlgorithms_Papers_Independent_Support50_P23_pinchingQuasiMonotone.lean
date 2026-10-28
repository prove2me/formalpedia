-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.pinchingQuasiMonotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:51:16.902906+00:00
-- url     : https://prove2.me/submissions/ad6d4a1d-30a3-4715-9e20-df3f06468557

import Mathlib

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

section X5mod_PQ_Thm
open Matrix
open scoped ComplexOrder

namespace X5PQ

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem scalar_main (p q : Matrix I I ℂ) (hp : p * pᴴ = 1) (hq : q * qᴴ = 1)
    (lam mu : I → ℝ) (hl : ∀ a, 0 ≤ lam a) (hm : ∀ b, 0 ≤ mu b)
    (hs : ∀ a b, lam a ≠ 0 → mu b = 0 → (pᴴ * q) a b = 0)
    (α : ℝ) (h1 : 1 < α) (h2 : α ≤ 2) :
    ∑ i, (∑ a, lam a * ‖p i a‖ ^ 2) ^ α * (∑ b, mu b * ‖q i b‖ ^ 2) ^ (1 - α) ≤
      ∑ a, ∑ b, lam a ^ α * (if mu b = 0 then 0 else mu b ^ (1 - α)) * ‖(pᴴ * q) a b‖ ^ 2 := by
  set r := fun i => ∑ a, lam a * ‖p i a‖ ^ 2 with hr
  set s := fun i => ∑ b, mu b * ‖q i b‖ ^ 2 with hs'
  set o := pᴴ * q
  have hr0 : ∀ i, 0 ≤ r i := fun i => Finset.sum_nonneg fun a _ => mul_nonneg (hl a) (by positivity)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Finset.sum_nonneg fun a _ => mul_nonneg (hm a) (by positivity)
  -- support in the form needed by `key`
  have hz : ∀ a b, mu b = 0 → (lam a : ℂ) * o a b = 0 := by
    intro a b hb
    by_cases ha : lam a = 0
    · simp [ha]
    · simp [o, hs a b ha hb]
  have hzero : ∀ a b, mu b = 0 → ‖o a b‖ ^ 2 * lam a ^ 2 = 0 := by
    intro a b hb
    have := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hz a b hb)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, norm_zero] at this
    linarith [this]
  rcases h2.lt_or_eq with h2 | h2
  · have hα : α ∈ Set.Ioo 1 2 := ⟨h1, h2⟩
    have hne : (1 - α) ≠ 0 := by linarith
    set S := Finset.univ.filter (fun i => s i ≠ 0)
    set T := (Finset.univ : Finset (I × I)).filter (fun k => mu k.2 ≠ 0)
    have hL : ∑ i, r i ^ α * s i ^ (1 - α) = ∑ i ∈ S, r i ^ α * s i ^ (1 - α) := by
      refine (Finset.sum_filter_of_ne fun i _ h => ?_).symm
      intro h0; apply h; rw [h0, Real.zero_rpow hne, mul_zero]
    have hR : ∑ a, ∑ b, lam a ^ α * (if mu b = 0 then 0 else mu b ^ (1 - α)) * ‖o a b‖ ^ 2 =
        ∑ k ∈ T, ‖o k.1 k.2‖ ^ 2 * (lam k.1 ^ α * mu k.2 ^ (1 - α)) := by
      rw [← Fintype.sum_prod_type' (f := fun a b =>
        lam a ^ α * (if mu b = 0 then 0 else mu b ^ (1 - α)) * ‖o a b‖ ^ 2)]
      rw [← Finset.sum_filter_of_ne (p := fun k : I × I => mu k.2 ≠ 0) fun k _ h => ?_]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_neg (Finset.mem_filter.1 hk).2]; ring
      · intro h0; apply h; simp [h0]
    rw [hL, hR]
    refine int_cmp S T r s (fun k => lam k.1) (fun k => mu k.2) (fun k => ‖o k.1 k.2‖ ^ 2) hα
      (fun i _ => hr0 i) (fun i hi => lt_of_le_of_ne (hs0 i) (Finset.mem_filter.1 hi).2.symm)
      (fun k _ => hl k.1) (fun k hk => lt_of_le_of_ne (hm k.2) (Finset.mem_filter.1 hk).2.symm) ?_
    intro t ht
    have hk := key p q hp hq lam mu 1 t zero_le_one ht.le hl hm (fun a b h0 => by
      have : lam a = 0 := by nlinarith [hl a, hm b, mul_nonneg ht.le (hm b)]
      simp [this])
    simp only [one_mul] at hk
    calc ∑ i ∈ S, r i ^ 2 / (r i + t * s i) ≤ ∑ i, r i ^ 2 / (r i + t * s i) :=
          Finset.sum_le_univ_sum_of_nonneg fun i => div_nonneg (sq_nonneg _)
            (add_nonneg (hr0 i) (mul_nonneg ht.le (hs0 i)))
      _ ≤ _ := hk
      _ = ∑ k ∈ T, ‖o k.1 k.2‖ ^ 2 * (lam k.1 ^ 2 / (lam k.1 + t * mu k.2)) := by
        rw [← Fintype.sum_prod_type' (f := fun a b => ‖o a b‖ ^ 2 * lam a ^ 2 / (lam a + t * mu b))]
        rw [← Finset.sum_filter_of_ne (p := fun k : I × I => mu k.2 ≠ 0) fun k _ h => ?_]
        · exact Finset.sum_congr rfl fun k _ => by ring
        · intro h0; apply h; rw [hzero k.1 k.2 h0, zero_div]
  · subst h2
    have hk := key p q hp hq lam mu 0 1 le_rfl zero_le_one hl hm (fun a b h0 => hz a b (by linarith))
    simp only [zero_mul, one_mul, zero_add] at hk
    have e1 : ∀ x : ℝ, x ^ (1 - 2 : ℝ) = x⁻¹ := fun x => by norm_num [Real.rpow_neg_one]
    calc ∑ i, r i ^ (2 : ℝ) * s i ^ (1 - 2 : ℝ) = ∑ i, r i ^ 2 / s i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [e1, Real.rpow_two, div_eq_mul_inv]
      _ ≤ _ := hk
      _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [e1, Real.rpow_two]
        split_ifs with hb
        · rw [hb, div_zero]; ring
        · rw [div_eq_mul_inv]; ring

lemma diag_re (U : Matrix I I ℂ) {R : Matrix I I ℂ} (hR : R.IsHermitian) (i : I) :
    ((Uᴴ * R * U) i i).re =
      ∑ a, hR.eigenvalues a * ‖(Uᴴ * (hR.eigenvectorUnitary : Matrix I I ℂ)) i a‖ ^ 2 := by
  set E := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set P := Uᴴ * E
  have hRe : R = E * diagonal (fun a => ((hR.eigenvalues a : ℝ) : ℂ)) * Eᴴ := by
    conv_lhs => rw [hR.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]; rfl
  have e : Uᴴ * R * U = Pᴴᴴ * diagonal (fun a => ((hR.eigenvalues a : ℝ) : ℂ)) * Pᴴ := by
    conv_lhs => rw [hRe]
    rw [conjTranspose_conjTranspose]
    simp only [P, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, diag_sandwich, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conjTranspose_apply, norm_star]

theorem main (rho N : Matrix I I ℂ) (hrho : rho.PosSemidef) (hN : N.PosSemidef)
    (hsupp : LinearMap.ker N.mulVecLin ≤ LinearMap.ker rho.mulVecLin)
    (U : Matrix.unitaryGroup I ℂ) (alpha : ℝ) (halpha : 1 < alpha) (halpha2 : alpha ≤ 2) :
    ∑ i, (((U : Matrix I I ℂ)ᴴ * rho * U) i i).re ^ alpha *
        (((U : Matrix I I ℂ)ᴴ * N * U) i i).re ^ (1 - alpha) ≤
      (cfc (fun x : ℝ => x ^ alpha) rho *
        cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - alpha)) N).trace.re := by
  set hR := hrho.isHermitian
  set hNh := hN.isHermitian
  set E := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set F := (hNh.eigenvectorUnitary : Matrix I I ℂ)
  set V := (U : Matrix I I ℂ)
  have hV : V * Vᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem U.2
  have hV' : Vᴴ * V = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem U.2
  have hE : E * Eᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hR.eigenvectorUnitary.2
  have hF : F * Fᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hNh.eigenvectorUnitary.2
  have hp : (Vᴴ * E) * (Vᴴ * E)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc E, hE,
      Matrix.one_mul, hV']
  have hq : (Vᴴ * F) * (Vᴴ * F)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc F, hF,
      Matrix.one_mul, hV']
  have ho : (Vᴴ * E)ᴴ * (Vᴴ * F) = X5OL.ov hR hNh := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc V, hV,
      Matrix.one_mul]
    simp only [X5OL.ov, star_eq_conjTranspose, E, F]
  have := scalar_main (Vᴴ * E) (Vᴴ * F) hp hq hR.eigenvalues hNh.eigenvalues hrho.eigenvalues_nonneg
    hN.eigenvalues_nonneg (fun a b ha hb => by rw [ho]; exact X5OL.supp_fwd hR hNh hsupp a b ha hb)
    alpha halpha halpha2
  simp only [diag_re V hR, diag_re V hNh]
  refine this.trans (le_of_eq ?_)
  rw [X5OL.tr_cfc_cfc hR hNh, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.ofReal_re, ho, X5OL.w]

end X5PQ
end X5mod_PQ_Thm

open scoped Matrix ComplexOrder

theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (rho N : Matrix I I ℂ) (hrho : rho.PosSemidef) (hN : N.PosSemidef)
    (hsupp : LinearMap.ker N.mulVecLin ≤ LinearMap.ker rho.mulVecLin)
    (U : Matrix.unitaryGroup I ℂ) (alpha : ℝ) (halpha : 1 < alpha) (halpha2 : alpha ≤ 2) :
    ∑ i, (((U : Matrix I I ℂ)ᴴ * rho * U) i i).re ^ alpha *
        (((U : Matrix I I ℂ)ᴴ * N * U) i i).re ^ (1 - alpha) ≤
      (cfc (fun x : ℝ => x ^ alpha) rho *
        cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - alpha)) N).trace.re :=
  X5PQ.main rho N hrho hN hsupp U alpha halpha halpha2

