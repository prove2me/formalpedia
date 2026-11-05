-- Prove2me | solution 1 for SpikedWishart.SoftEdge.theorem_1_1_a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:29:11.217117+00:00
-- url     : https://prove2.me/submissions/5596159f-9184-4404-a993-0c7c60be2349

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Model
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
import Theorems.Thm_SpikedWishart_SoftEdge_proposition_2_1
import Theorems.Thm_SpikedWishart_SoftEdge_proposition_3_1
import Theorems.Thm_SpikedWishart_SoftEdge_eq_200
import Theorems.Thm_SpikedWishart_SoftEdge_kernelKMN_factorization
import Theorems.Thm_SpikedWishart_SoftEdge_eq_200_k_zero
import Theorems.Thm_SpikedWishart_SoftEdge_fredholmDet_tendsto_of_factored_kernels

set_option autoImplicit false


set_option autoImplicit false

namespace Lib5e

open MeasureTheory Filter Topology Set Complex

/-- A cubic with leading coefficient `-1/3` is bounded above on `[0, ∞)`. -/
theorem cubic_bound (A B : ℝ) : ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t → A * t + B * t ^ 2 - t ^ 3 / 3 ≤ D := by
  have hL0 : 0 ≤ |A| + |B| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨(|A| + |B|) + 9 * (|A| + |B|) ^ 3, fun t ht => ?_⟩
  have hA : A * t ≤ |A| * t := mul_le_mul_of_nonneg_right (le_abs_self A) ht
  have hB : B * t ^ 2 ≤ |B| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg t)
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have hL3 : 0 ≤ (|A| + |B|) ^ 3 := pow_nonneg hL0 3
  rcases le_total t 1 with h1 | h1
  · have h1A : |A| * t ≤ |A| := mul_le_of_le_one_right (abs_nonneg A) h1
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have h1B : |B| * t ^ 2 ≤ |B| := mul_le_of_le_one_right (abs_nonneg B) ht2
    linarith
  · have hAt : |A| * t ≤ |A| * t ^ 2 := by
      have : t ≤ t ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (abs_nonneg A)
    rcases le_total t (3 * (|A| + |B|)) with h2 | h2
    · have h9 : t ^ 2 ≤ 9 * (|A| + |B|) ^ 2 := by nlinarith
      have h9' := mul_le_mul_of_nonneg_left h9 hL0
      nlinarith
    · have hneg := mul_nonneg (sq_nonneg t) (sub_nonneg.2 h2)
      nlinarith

/-- Norm bound for one ray integral from an exponentially decaying integrand bound. -/
theorem ray_integral_norm_le (φ : ℂ → ℂ) (c : ℂ) (θ B : ℝ)
    (h : ∀ t : ℝ, 0 < t → ‖φ (c + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t)) :
    ‖∫ t in Ioi (0 : ℝ), φ (c + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B := by
  have hg : Integrable (fun t : ℝ => B * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) B
  have hb : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖φ (c + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    exact h t ht
  refine (norm_integral_le_of_norm_le hg hb).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one]

theorem re_cube (a : ℂ) : (a ^ 3).re = a.re ^ 3 - 3 * a.re * a.im ^ 2 := by
  rw [show a ^ 3 = a * a * a by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]
  ring

theorem ray_point_re_im (c t θ : ℝ) :
    ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)).re = c + t * Real.cos θ ∧
      ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)).im = t * Real.sin θ := by
  constructor
  · rw [Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im]
    ring
  · rw [Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]
    ring

/-- Pointwise bound for the `𝓗_∞` integrand on a ray `c + t e^{iθ}` with `cos θ = 1/2`. -/
theorem H_integrand_bound (c x0 θ D : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + 1) * t + (-c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (u : ℝ) (hu : x0 ≤ u) (t : ℝ) (ht : 0 < t) :
    ‖exp (-(u : ℂ) * ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
        ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
        (1 / ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ k)‖ ≤
      ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) * Real.exp (-t) := by
  set a : ℂ := (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im c t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : (-(u : ℂ) * a + a ^ 3 / 3).re = -u * a.re + (a.re ^ 3 - 3 * a.re * a.im ^ 2) / 3 := by
    rw [Complex.add_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, ofReal_re, ofReal_im]
    ring
  have hexp : (-(u : ℂ) * a + a ^ 3 / 3).re ≤ D + c ^ 3 / 3 + -c * u + -t := by
    rw [hwre, him2, hre]
    have h1 := hD t ht.le
    have h2 := mul_nonneg (sub_nonneg.2 hu) ht.le
    nlinarith
  have hnorm2 : (-c / 2) ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    nlinarith [sq_nonneg (t + c / 2), him2, sq_nonneg a.im]
  have hc2 : 0 < -c / 2 := by linarith
  have hnorm : -c / 2 ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg a) hlt
    nlinarith
  have hinv : 1 / ‖a‖ ≤ 2 / -c := by
    have := one_div_le_one_div_of_le hc2 hnorm
    calc 1 / ‖a‖ ≤ 1 / (-c / 2) := this
      _ = 2 / -c := by field_simp
  have hk : ‖1 / a ^ k‖ ≤ (2 / -c) ^ k := by
    rw [norm_div, norm_one, norm_pow, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hinv k
  rw [norm_mul, norm_exp]
  calc Real.exp (-(u : ℂ) * a + a ^ 3 / 3).re * ‖1 / a ^ k‖
      ≤ Real.exp (D + c ^ 3 / 3 + -c * u + -t) * (2 / -c) ^ k :=
        mul_le_mul (Real.exp_le_exp.2 hexp) hk (norm_nonneg _) (Real.exp_pos _).le
    _ = ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) * Real.exp (-t) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring

/-- Pointwise bound for the `𝓙_∞` integrand on a ray `c + t e^{iθ}` with `cos θ = -1/2`. -/
theorem J_integrand_bound (c x0 θ D : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = -1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + 2) * t + (c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (v : ℝ) (hv : x0 ≤ v) (t : ℝ) (ht : 0 < t) :
    ‖exp ((v : ℂ) * ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) -
        ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
        ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ k‖ ≤
      ((k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v)) * Real.exp (-t) := by
  set a : ℂ := (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im c t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : ((v : ℂ) * a - a ^ 3 / 3).re = v * a.re - (a.re ^ 3 - 3 * a.re * a.im ^ 2) / 3 := by
    rw [Complex.sub_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, ofReal_re, ofReal_im]
    ring
  have hexp : ((v : ℂ) * a - a ^ 3 / 3).re + (-c + t) ≤ (D - c ^ 3 / 3 - c) + c * v + -t := by
    rw [hwre, him2, hre]
    have h1 := hD t ht.le
    have h2 := mul_nonneg (sub_nonneg.2 hv) ht.le
    nlinarith
  have hna : ‖a‖ ≤ -c + t := by
    calc ‖a‖ ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * exp ((θ : ℂ) * I)‖ := norm_add_le _ _
      _ = -c + t := by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hc, abs_of_pos ht]
  have hx0 : 0 ≤ -c + t := by linarith
  have hfac : (-c + t) ^ k ≤ Real.exp (-c + t) * k.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := -c + t) hx0 k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rwa [div_le_iff₀ hf] at h
  have hk : ‖a ^ k‖ ≤ Real.exp (-c + t) * k.factorial := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg a) hna k).trans hfac
  rw [norm_mul, norm_exp]
  calc Real.exp ((v : ℂ) * a - a ^ 3 / 3).re * ‖a ^ k‖
      ≤ Real.exp ((v : ℂ) * a - a ^ 3 / 3).re * (Real.exp (-c + t) * k.factorial) :=
        mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    _ = Real.exp (((v : ℂ) * a - a ^ 3 / 3).re + (-c + t)) * k.factorial := by
        rw [← mul_assoc, ← Real.exp_add]
    _ ≤ Real.exp ((D - c ^ 3 / 3 - c) + c * v + -t) * k.factorial :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hexp) (by positivity)
    _ = ((k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v)) * Real.exp (-t) := by
        rw [Real.exp_add, Real.exp_add]; ring


theorem sin_pi_div_three_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

open SpikedWishart.SoftEdge in
/-- R7a. `|𝓗_∞(u)| ≤ C e^{-(ε+c)u}` on `[x₀, ∞)` for a vertex `c < 0`. -/
theorem Hinf_bound (ε : ℝ) (k : ℕ) (c x0 : ℝ) (hc : c < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, x0 ≤ u → ‖Hinf ε k c u‖ ≤ C * Real.exp (-(ε + c) * u) := by
  obtain ⟨D, hD⟩ := cubic_bound (-x0 / 2 + c ^ 2 / 2 + 1) (-c / 2)
  have h2c : 0 ≤ 2 / -c := div_nonneg (by norm_num) (by linarith)
  have hB0 : 0 ≤ (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) := by positivity
  refine ⟨(2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) / Real.pi, div_nonneg hB0 Real.pi_pos.le,
    fun u hu => ?_⟩
  have hcos1 : Real.cos (-Real.pi / 3) = 1 / 2 := by
    rw [neg_div, Real.cos_neg, Real.cos_pi_div_three]
  have hsin1 : Real.sin (-Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [neg_div, Real.sin_neg, neg_sq, sin_pi_div_three_sq]
  have hray : ∀ θ : ℝ, Real.cos θ = 1 / 2 → Real.sin θ ^ 2 = 3 / 4 →
      ‖∫ t in Ioi (0 : ℝ), (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤
        (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u) := by
    intro θ h1 h2
    refine ray_integral_norm_le (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))
      (c : ℂ) θ _ (fun t ht => ?_)
    exact H_integrand_bound c x0 θ D k hc h1 h2 hD u hu t ht
  have hR : ‖rayIntegral (c : ℂ) (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))‖ ≤
        2 * ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) := by
    unfold rayIntegral
    refine (norm_sub_le _ _).trans ?_
    calc _ ≤ (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u) +
          (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u) :=
          add_le_add (hray (-Real.pi / 3) hcos1 hsin1)
            (hray (Real.pi / 3) Real.cos_pi_div_three sin_pi_div_three_sq)
      _ = _ := by ring
  unfold Hinf
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hR (by positivity)).trans (le_of_eq ?_)
  have he : Real.exp (-(ε + c) * u) = Real.exp (-ε * u) * Real.exp (-c * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  field_simp

open SpikedWishart.SoftEdge in
/-- R7b. `|𝓙_∞(v)| ≤ C e^{(ε+c)v}` on `[x₀, ∞)` for a vertex `c < 0`. -/
theorem Jinf_bound (ε : ℝ) (k : ℕ) (c x0 : ℝ) (hc : c < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, x0 ≤ v → ‖Jinf ε k c v‖ ≤ C * Real.exp ((ε + c) * v) := by
  obtain ⟨D, hD⟩ := cubic_bound (-x0 / 2 + c ^ 2 / 2 + 2) (c / 2)
  have hB0 : 0 ≤ (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) := by positivity
  refine ⟨(k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) / Real.pi,
    div_nonneg hB0 Real.pi_pos.le, fun v hv => ?_⟩
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have hcos1 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hsin1 : Real.sin (2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [h23, Real.sin_pi_sub, sin_pi_div_three_sq]
  have hm : -2 * Real.pi / 3 = -(2 * Real.pi / 3) := by ring
  have hcos2 : Real.cos (-2 * Real.pi / 3) = -1 / 2 := by rw [hm, Real.cos_neg, hcos1]
  have hsin2 : Real.sin (-2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [hm, Real.sin_neg, neg_sq, hsin1]
  have hray : ∀ θ : ℝ, Real.cos θ = -1 / 2 → Real.sin θ ^ 2 = 3 / 4 →
      ‖∫ t in Ioi (0 : ℝ), (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤
        (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v) := by
    intro θ h1 h2
    refine ray_integral_norm_le (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)
      (c : ℂ) θ _ (fun t ht => ?_)
    exact J_integrand_bound c x0 θ D k hc h1 h2 hD v hv t ht
  have hR : ‖rayIntegral (c : ℂ) (-2 * Real.pi / 3) (2 * Real.pi / 3)
      (fun a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)‖ ≤
        2 * ((k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v)) := by
    unfold rayIntegral
    refine (norm_sub_le _ _).trans ?_
    calc _ ≤ (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v) +
          (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v) :=
          add_le_add (hray (2 * Real.pi / 3) hcos1 hsin1) (hray (-2 * Real.pi / 3) hcos2 hsin2)
      _ = _ := by ring
  unfold Jinf
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hR (by positivity)).trans (le_of_eq ?_)
  have he : Real.exp ((ε + c) * v) = Real.exp (ε * v) * Real.exp (c * v) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  field_simp

end Lib5e

namespace Lib5e

/-- R4. Conjugating a kernel by a nonvanishing function does not change the Fredholm minors. -/
theorem det_conj {n : ℕ} (a : ℝ → ℝ) (ha : ∀ t, a t ≠ 0) (K : ℝ → ℝ → ℝ) (u : Fin n → ℝ) :
    (Matrix.of fun i j => a (u i) * K (u i) (u j) / a (u j)).det =
      (Matrix.of fun i j => K (u i) (u j)).det := by
  have hM : (Matrix.of fun i j => a (u i) * K (u i) (u j) / a (u j)) =
      Matrix.diagonal (fun i => a (u i)) * (Matrix.of fun i j => K (u i) (u j)) *
        Matrix.diagonal (fun i => (a (u i))⁻¹) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp [ha]

/-- Scaling every entry of an `n × n` matrix by `s` multiplies the determinant by `s ^ n`. -/
theorem det_smul_kernel {n : ℕ} (s : ℝ) (K : ℝ → ℝ → ℝ) (u : Fin n → ℝ) :
    (Matrix.of fun i j => s * K (u i) (u j)).det = s ^ n * (Matrix.of fun i j => K (u i) (u j)).det := by
  have : (Matrix.of fun i j => s * K (u i) (u j)) = s • (Matrix.of fun i j => K (u i) (u j)) := by
    ext i j; simp
  rw [this, Matrix.det_smul, Fintype.card_fin]


open MeasureTheory Filter Topology Set

/-- R5. Affine change of variables `u = ξ₀ + s w` (`s > 0`) in the `n`-th Fredholm term. -/
theorem term_affine {n : ℕ} (K : ℝ → ℝ → ℝ) (ξ0 s x : ℝ) (hs : 0 < s) :
    ∫ u in Set.univ.pi (fun _ : Fin n => Ioi (ξ0 + s * x)),
        (Matrix.of fun p q => K (u p) (u q)).det =
      ∫ w in Set.univ.pi (fun _ : Fin n => Ioi x),
        (Matrix.of fun p q => s * K (ξ0 + s * w p) (ξ0 + s * w q)).det := by
  set S := Set.univ.pi (fun _ : Fin n => Ioi (ξ0 + s * x)) with hSdef
  set S' := Set.univ.pi (fun _ : Fin n => Ioi x) with hS'def
  let F : (Fin n → ℝ) → ℝ := fun u => (Matrix.of fun p q => K (u p) (u q)).det
  let c : Fin n → ℝ := fun _ => ξ0
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hS' : MeasurableSet S' := MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hmem : ∀ w : Fin n → ℝ, (c + s • w ∈ S ↔ w ∈ S') := by
    intro w
    show (∀ p ∈ Set.univ, (c + s • w) p ∈ Ioi (ξ0 + s * x)) ↔ (∀ p ∈ Set.univ, w p ∈ Ioi x)
    refine forall₂_congr (fun p _ => ?_)
    show ξ0 + s * x < ξ0 + s * w p ↔ x < w p
    constructor
    · intro h
      exact lt_of_mul_lt_mul_left (by linarith) hs.le
    · intro h
      have := mul_lt_mul_of_pos_left h hs
      linarith
  have h1 : ∀ w : Fin n → ℝ,
      (Matrix.of fun p q => s * K (ξ0 + s * w p) (ξ0 + s * w q)).det = s ^ n * F (c + s • w) := by
    intro w
    exact det_smul_kernel s (fun a b => K (ξ0 + s * a) (ξ0 + s * b)) w
  have hsn : 0 < s ^ n := pow_pos hs n
  have hcs : ∫ w, S.indicator F (c + s • w) = |(s ^ n)⁻¹| * ∫ u, S.indicator F u := by
    have h := Measure.integral_comp_smul (volume : Measure (Fin n → ℝ))
      (fun y => S.indicator F (c + y)) s
    beta_reduce at h
    rw [h, integral_add_left_eq_self (μ := volume) (f := S.indicator F) c,
      Module.finrank_fin_fun, smul_eq_mul]
  calc ∫ u in S, F u = ∫ u, S.indicator F u := (integral_indicator hS).symm
    _ = s ^ n * (|(s ^ n)⁻¹| * ∫ u, S.indicator F u) := by
        rw [abs_of_pos (inv_pos.2 hsn), ← mul_assoc, mul_inv_cancel₀ hsn.ne', one_mul]
    _ = s ^ n * ∫ w, S.indicator F (c + s • w) := by rw [hcs]
    _ = ∫ w, S'.indicator (fun w => s ^ n * F (c + s • w)) w := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        by_cases hw : w ∈ S'
        · simp only [Set.indicator_of_mem hw, Set.indicator_of_mem ((hmem w).2 hw)]
        · simp only [Set.indicator_of_notMem hw,
            Set.indicator_of_notMem (fun h => hw ((hmem w).1 h)), mul_zero]
    _ = ∫ w in S', s ^ n * F (c + s • w) := integral_indicator hS'
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        exact (h1 w).symm

end Lib5e

namespace Lib5e

open MeasureTheory Filter Topology Set Complex
open SpikedWishart.SoftEdge

/-! R9: assembly of BBP Theorem 1.1(a) from P21, P31, E200 and the R1-R8 library. -/

/-- Left/right ends of the `Γ` contour: `L = (q + pc)/2`, `R = max 1 c⁻¹ + 1`. -/
noncomputable def cGam (γ q c : ℝ) : ℝ := ((q + pc γ) / 2 + (max 1 c⁻¹ + 1)) / 2
noncomputable def rGam (γ q c : ℝ) : ℝ := ((max 1 c⁻¹ + 1) - (q + pc γ) / 2) / 2

/-- The `r` spikes `π_j = 1/ℓ_j`, `j < r`. -/
noncomputable def piR {N : ℕ} (r : ℕ) (hr : r ≤ N) (ℓ : Fin N → ℝ) : Fin r → ℝ :=
  fun j => (ℓ ⟨j, lt_of_lt_of_le j.2 hr⟩)⁻¹

/-- `Z_M H(u)` with `ε = 1`. -/
noncomputable def HnF {N r : ℕ} (k M : ℕ) (hr : r ≤ N) (γ c : ℝ) (ℓ : Fin N → ℝ) : ℝ → ℂ :=
  fun w => ZM γ (qM γ 1 M) M k (piR r hr ℓ) *
    Hcal γ (qM γ 1 M) M k (piR r hr ℓ) (cGam γ (qM γ 1 M) c) (rGam γ (qM γ 1 M) c) w

/-- `J(v)/Z_M` with `ε = 1`, `Σ` the circle of centre `0` and radius `q/2`. -/
noncomputable def JnF {N r : ℕ} (k M : ℕ) (hr : r ≤ N) (γ c : ℝ) (ℓ : Fin N → ℝ) : ℝ → ℂ :=
  fun w => Jcal γ (qM γ 1 M) M k (piR r hr ℓ) 0 (qM γ 1 M / 2) w / ZM γ (qM γ 1 M) M k (piR r hr ℓ)

theorem pc_inv {γ : ℝ} (hγ : 0 < γ) : (1 + γ⁻¹)⁻¹ = pc γ := by
  rw [pc]; field_simp <;> ring

theorem pc_lt_one {γ : ℝ} (hγ : 1 ≤ γ) : pc γ < 1 := by
  rw [pc, div_lt_one (by linarith)]; linarith

theorem half_le_pc {γ : ℝ} (hγ : 1 ≤ γ) : 1 / 2 ≤ pc γ := by
  rw [pc, le_div_iff₀ (by linarith)]; linarith

theorem nu_pos {γ : ℝ} (hγ : 0 < γ) : 0 < nu γ :=
  div_pos (Real.rpow_pos_of_pos (by linarith) _) hγ

theorem one_lt_nu {γ : ℝ} (hγ : 1 ≤ γ) : 1 < nu γ := by
  have h1 : (1 + γ) ^ (1 : ℝ) ≤ (1 + γ) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_one] at h1
  rw [nu, one_lt_div (by linarith)]; linarith

theorem nu_le {γ γ₀ : ℝ} (hγ : 1 ≤ γ) (hγ₀ : γ ≤ γ₀) : nu γ ≤ (1 + γ₀) ^ (4 / 3 : ℝ) := by
  have h1 : (1 + γ) ^ (4 / 3 : ℝ) ≤ (1 + γ₀) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  exact (div_le_self (Real.rpow_pos_of_pos (by linarith) _).le hγ).trans h1

theorem one_le_mu {γ : ℝ} (hγ : 1 ≤ γ) : 1 ≤ mu γ := by
  rw [mu]; apply one_le_pow₀; rw [le_div_iff₀ (by linarith)]; linarith

theorem q_facts {γ : ℝ} {M : ℕ} (hγ : 1 ≤ γ) (ht : 3 ≤ (M : ℝ) ^ (1 / 3 : ℝ)) :
    0 < qM γ 1 M ∧ qM γ 1 M < pc γ := by
  have hν := one_lt_nu hγ
  have ht0 : 0 < (M : ℝ) ^ (1 / 3 : ℝ) := by linarith
  have h2 : 2 < nu γ * (M : ℝ) ^ (1 / 3 : ℝ) := by nlinarith
  have h3 : 1 / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num) h2
  have h4 : 0 < 1 / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) := by positivity
  have h5 := half_le_pc hγ
  have hq : qM γ 1 M = pc γ - 1 / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) := rfl
  rw [hq]; constructor <;> linarith

theorem xi_nonneg {γ γ₀ x : ℝ} {M : ℕ} (hγ : 1 ≤ γ) (hγ₀ : γ ≤ γ₀) (hM : 0 < M)
    (ht : max 3 ((1 + γ₀) ^ (4 / 3 : ℝ) * |x| + 1) ≤ (M : ℝ) ^ (1 / 3 : ℝ)) :
    0 ≤ mu γ + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * x := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : ((M : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMr.le]; norm_num
  have hmu := one_le_mu hγ
  have hνl := nu_le hγ hγ₀
  have hν0 := nu_pos (by linarith : (0 : ℝ) < γ)
  have ht1 := le_max_left 3 ((1 + γ₀) ^ (4 / 3 : ℝ) * |x| + 1)
  have ht2 := le_max_right 3 ((1 + γ₀) ^ (4 / 3 : ℝ) * |x| + 1)
  generalize (M : ℝ) ^ (1 / 3 : ℝ) = t at ht h3 ht1 ht2
  rw [← h3]
  have ht0 : 0 < t := by linarith
  have hs : nu γ * t / t ^ 3 = nu γ / t ^ 2 := by field_simp <;> ring
  rw [hs]
  have hνx : nu γ * |x| ≤ t ^ 2 := by
    have : nu γ * |x| ≤ (1 + γ₀) ^ (4 / 3 : ℝ) * |x| :=
      mul_le_mul_of_nonneg_right hνl (abs_nonneg x)
    nlinarith
  have hb : nu γ / t ^ 2 * |x| ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; exact hνx
  have hc : -(nu γ / t ^ 2 * |x|) ≤ nu γ / t ^ 2 * x := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le x) (by positivity)
  linarith

theorem event_iff (γ x lam : ℝ) (M : ℕ) (hγ : 1 ≤ γ) (hM : 0 < M) :
    (lam - (1 + γ⁻¹) ^ 2) * (γ / (1 + γ) ^ (4 / 3 : ℝ)) * (M : ℝ) ^ (2 / 3 : ℝ) ≤ x ↔
      lam ≤ mu γ + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * x := by
  have hγ0 : 0 < γ := by linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : ((M : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMr.le]; norm_num
  have h2 : (M : ℝ) ^ (2 / 3 : ℝ) = ((M : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMr.le]; norm_num
  have ht : 0 < (M : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hMr _
  have hmu : (1 + γ⁻¹) ^ 2 = mu γ := by
    rw [mu, div_eq_mul_inv, add_mul, one_mul, mul_inv_cancel₀ hγ0.ne', add_comm]
  have hB : 0 < (1 + γ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [h2, hmu, nu]
  generalize (M : ℝ) ^ (1 / 3 : ℝ) = t at h3 ht ⊢
  rw [← h3]
  generalize (1 + γ) ^ (4 / 3 : ℝ) = B at hB ⊢
  have hP : 0 < γ / B * t ^ 2 := by positivity
  rw [mul_assoc, ← le_div_iff₀ hP, sub_le_iff_le_add']
  have : x / (γ / B * t ^ 2) = B / γ * t / t ^ 3 * x := by field_simp <;> ring
  rw [this]

theorem sphere_ne {c ρ p : ℝ} (h : |p - c| ≠ ρ) {z : ℂ} (hz : z ∈ Metric.sphere (c : ℂ) ρ) :
    (p : ℂ) - z ≠ 0 := by
  intro h0
  have hzp : z = p := (sub_eq_zero.mp h0).symm
  rw [hzp, mem_sphere_iff_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hz
  exact h hz

theorem in_gam {γ q c p : ℝ} (hq : q < pc γ) (h1 : pc γ ≤ p) (h2 : p ≤ max 1 c⁻¹) :
    |p - cGam γ q c| < rGam γ q c := by
  unfold cGam rGam; rw [abs_sub_lt_iff]; constructor <;> linarith

theorem pi_bounds {N r : ℕ} (k : ℕ) (γ c : ℝ) (hc : 0 < c) (hγ : 1 ≤ γ) (ℓ : Fin N → ℝ)
    (hℓ_one : ∀ j : Fin N, r ≤ (j : ℕ) → ℓ j = 1)
    (hℓ_crit : ∀ j : Fin N, (j : ℕ) < k → ℓ j = 1 + γ⁻¹)
    (hℓ_sub : ∀ j : Fin N, k ≤ (j : ℕ) → (j : ℕ) < r → c ≤ ℓ j ∧ ℓ j ≤ 1 + γ⁻¹ - c)
    (j : Fin N) :
    0 < ℓ j ∧ pc γ ≤ (ℓ j)⁻¹ ∧ (ℓ j)⁻¹ ≤ max 1 c⁻¹ ∧
      (k ≤ (j : ℕ) → (j : ℕ) < r → pc γ < (ℓ j)⁻¹) := by
  have hγ0 : 0 < γ := by linarith
  have hpc1 := pc_lt_one hγ
  have hpcinv := pc_inv hγ0
  have hg : 0 < 1 + γ⁻¹ := by positivity
  by_cases h1 : r ≤ (j : ℕ)
  · rw [hℓ_one j h1, inv_one]
    exact ⟨one_pos, hpc1.le, le_max_left _ _, fun _ h' => absurd h' (not_lt.mpr h1)⟩
  · push_neg at h1
    by_cases h2 : (j : ℕ) < k
    · rw [hℓ_crit j h2, hpcinv]
      exact ⟨hg, le_rfl, hpc1.le.trans (le_max_left _ _), fun h _ => absurd h (not_le.mpr h2)⟩
    · push_neg at h2
      obtain ⟨hl1, hl2⟩ := hℓ_sub j h2 h1
      have hl0 : 0 < ℓ j := lt_of_lt_of_le hc hl1
      have hlt : pc γ < (ℓ j)⁻¹ := by
        rw [← hpcinv]; exact (inv_lt_inv₀ hg hl0).mpr (by linarith)
      refine ⟨hl0, hlt.le, ?_, fun _ _ => hlt⟩
      exact ((inv_le_inv₀ hl0 hc).mpr hl1).trans (le_max_right _ _)

theorem ZM_ne {r : ℕ} (k M : ℕ) (γ q : ℝ) (hγ : 1 ≤ γ) (hM : 0 < M) (π' : Fin r → ℝ)
    (hπ : ∀ j : Fin r, k ≤ (j : ℕ) → pc γ < π' j) : ZM γ q M k π' ≠ 0 := by
  have hpc1 := pc_lt_one hγ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hσ : 0 < nu γ * (M : ℝ) ^ (1 / 3 : ℝ) :=
    mul_pos (nu_pos (by linarith)) (Real.rpow_pos_of_pos hMr _)
  have h1pc : (1 : ℂ) - (pc γ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    exact (sub_pos.mpr hpc1).ne'
  unfold ZM gFn
  refine div_ne_zero (mul_ne_zero (one_div_ne_zero (pow_ne_zero _ h1pc))
    (Finset.prod_ne_zero_iff.mpr fun j hj => ?_))
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hσ.ne')))
      (Complex.exp_ne_zero _))
  rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
  exact (sub_pos.mpr (hπ j (Finset.mem_filter.mp hj).2)).ne'

/-- All contour facts for one `n`. -/
theorem bundle {N r : ℕ} (k : ℕ) (hr : r ≤ N) (γ c q : ℝ) (hc : 0 < c) (hγ : 1 ≤ γ)
    (hq0 : 0 < q) (hq : q < pc γ) (ℓ : Fin N → ℝ)
    (hℓ_one : ∀ j : Fin N, r ≤ (j : ℕ) → ℓ j = 1)
    (hℓ_crit : ∀ j : Fin N, (j : ℕ) < k → ℓ j = 1 + γ⁻¹)
    (hℓ_sub : ∀ j : Fin N, k ≤ (j : ℕ) → (j : ℕ) < r → c ≤ ℓ j ∧ ℓ j ≤ 1 + γ⁻¹ - c) :
    (∀ j : Fin r, (j : ℕ) < k → piR r hr ℓ j = pc γ) ∧
    (∀ j : Fin r, k ≤ (j : ℕ) → c ≤ (piR r hr ℓ j)⁻¹ ∧ (piR r hr ℓ j)⁻¹ ≤ 1 + γ⁻¹ - c) ∧
    |pc γ - cGam γ q c| < rGam γ q c ∧ (∀ j : Fin r, |piR r hr ℓ j - cGam γ q c| < rGam γ q c) ∧
    |1 - cGam γ q c| < rGam γ q c ∧ q < cGam γ q c - rGam γ q c ∧ 0 ≤ rGam γ q c ∧
    (∀ j : Fin N, |(ℓ j)⁻¹ - cGam γ q c| < rGam γ q c) ∧ (∀ j, 0 < ℓ j) ∧
    (∀ j : Fin N, q < (ℓ j)⁻¹) ∧
    (∀ z ∈ Metric.sphere (cGam γ q c : ℂ) (rGam γ q c),
      z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j : Fin N, (((ℓ j)⁻¹ : ℝ) : ℂ) - z ≠ 0) ∧
    (∀ z ∈ Metric.sphere (cGam γ q c : ℂ) (rGam γ q c),
      z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j : Fin r, ((piR r hr ℓ j : ℝ) : ℂ) - z ≠ 0) ∧
    (∀ w ∈ Metric.sphere ((0 : ℝ) : ℂ) (q / 2), w ≠ 0 ∧ 1 - w ≠ 0) ∧
    (∀ j : Fin r, k ≤ (j : ℕ) → pc γ < piR r hr ℓ j) := by
  have hγ0 : 0 < γ := by linarith
  have hpc1 := pc_lt_one hγ
  have hpcinv := pc_inv hγ0
  have hB := pi_bounds k γ c hc hγ ℓ hℓ_one hℓ_crit hℓ_sub
  have hmax : (1 : ℝ) ≤ max 1 c⁻¹ := le_max_left _ _
  have hL : q < cGam γ q c - rGam γ q c := by unfold cGam rGam; linarith
  have hR0 : 0 ≤ rGam γ q c := by unfold rGam; linarith
  have hc0 : rGam γ q c < cGam γ q c := by linarith
  have hpcG : |pc γ - cGam γ q c| < rGam γ q c := in_gam hq le_rfl (hpc1.le.trans hmax)
  have h1G : |1 - cGam γ q c| < rGam γ q c := in_gam hq hpc1.le hmax
  have hNG : ∀ j : Fin N, |(ℓ j)⁻¹ - cGam γ q c| < rGam γ q c :=
    fun j => in_gam hq (hB j).2.1 (hB j).2.2.1
  have hrG : ∀ j : Fin r, |piR r hr ℓ j - cGam γ q c| < rGam γ q c := fun j => hNG _
  have hz0 : ∀ z ∈ Metric.sphere (cGam γ q c : ℂ) (rGam γ q c), z ≠ 0 := by
    intro z hz h0
    have := sphere_ne (p := 0) (c := cGam γ q c) (ρ := rGam γ q c) (by
      rw [zero_sub, abs_neg, abs_of_pos (by linarith)]; exact hc0.ne') hz
    rw [Complex.ofReal_zero, zero_sub, neg_ne_zero] at this
    exact this h0
  have hz1 : ∀ z ∈ Metric.sphere (cGam γ q c : ℂ) (rGam γ q c), (1 : ℂ) - z ≠ 0 := by
    intro z hz
    have := sphere_ne (p := 1) h1G.ne hz
    rwa [Complex.ofReal_one] at this
  refine ⟨fun j hj => ?_, fun j hj => ?_, hpcG, hrG, h1G, hL, hR0, hNG, fun j => (hB j).1,
    fun j => lt_of_lt_of_le hq (hB j).2.1,
    fun z hz => ⟨hz0 z hz, hz1 z hz, fun j => sphere_ne (hNG j).ne hz⟩,
    fun z hz => ⟨hz0 z hz, hz1 z hz, fun j => sphere_ne (hrG j).ne hz⟩, fun w hw => ?_,
    fun j hj => (hB _).2.2.2 hj j.2⟩
  · show (ℓ _)⁻¹ = pc γ
    rw [hℓ_crit _ hj, hpcinv]
  · show c ≤ ((ℓ _)⁻¹)⁻¹ ∧ ((ℓ _)⁻¹)⁻¹ ≤ 1 + γ⁻¹ - c
    rw [inv_inv]; exact hℓ_sub _ hj j.2
  · constructor
    · intro h0
      have := sphere_ne (p := 0) (c := 0) (ρ := q / 2) (by
        rw [sub_zero, abs_zero]; linarith) hw
      rw [Complex.ofReal_zero, zero_sub, neg_ne_zero] at this
      exact this h0
    · have := sphere_ne (p := 1) (c := 0) (ρ := q / 2) (by
        rw [sub_zero, abs_one]; linarith) hw
      rwa [Complex.ofReal_one] at this

theorem exp_shift {ci c' A x w : ℝ} (h0 : c' ≤ ci) (hA : ci ≤ A) (hc' : 0 ≤ c') (hw : x ≤ w) :
    Real.exp (-ci * w) ≤ Real.exp (A * |x|) * Real.exp (-c' * w) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
  have h1 : (c' - ci) * w ≤ (c' - ci) * x := mul_le_mul_of_nonpos_left hw (by linarith)
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs x) (sub_nonneg.mpr h0)
  have h3 : (ci - c') * |x| ≤ A * |x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg x)
  linarith

theorem bnd {Ci S ci c' A x w : ℝ} (hCi : 0 ≤ Ci) (hS : Ci ≤ S) (h0 : c' ≤ ci) (hA : ci ≤ A)
    (hc' : 0 ≤ c') (hw : x ≤ w) :
    Ci * Real.exp (-ci * w) ≤ S * Real.exp (A * |x|) * Real.exp (-c' * w) := by
  calc Ci * Real.exp (-ci * w) ≤ Ci * (Real.exp (A * |x|) * Real.exp (-c' * w)) :=
        mul_le_mul_of_nonneg_left (exp_shift h0 hA hc' hw) hCi
    _ ≤ S * (Real.exp (A * |x|) * Real.exp (-c' * w)) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
    _ = _ := by ring

theorem bnd_t {Ci S ci c' A x w t : ℝ} (hCi : 0 ≤ Ci) (hS : Ci ≤ S) (h0 : c' ≤ ci) (hA : ci ≤ A)
    (hc' : 0 ≤ c') (hw : x ≤ w) (ht : 0 < t) :
    Ci * Real.exp (-ci * w) / t ≤ S * Real.exp (A * |x|) * Real.exp (-c' * w) * (1 / t) := by
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_right (bnd hCi hS h0 hA hc' hw) (by positivity)

/-- The pre-limit identity for one `n`. -/
theorem per_n {N r : ℕ} (k M : ℕ) (hkr : k ≤ r) (hr : r ≤ N) (γ c x : ℝ) (hc : 0 < c)
    (hγdef : γ = Real.sqrt ((M : ℝ) / N)) (hγ1 : 1 ≤ γ) (hN : 0 < N) (hNM : N ≤ M)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (hℓ_one : ∀ j : Fin N, r ≤ (j : ℕ) → ℓ j = 1)
    (hℓ_crit : ∀ j : Fin N, (j : ℕ) < k → ℓ j = 1 + γ⁻¹)
    (hℓ_sub : ∀ j : Fin N, k ≤ (j : ℕ) → (j : ℕ) < r → c ≤ ℓ j ∧ ℓ j ≤ 1 + γ⁻¹ - c)
    (hM : 0 < M) (ht : 3 ≤ (M : ℝ) ^ (1 / 3 : ℝ))
    (hξ : 0 ≤ mu γ + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * x) :
    (sampleLaw M N).real {G | (largestEig M U ℓ G - (1 + γ⁻¹) ^ 2) *
        (γ / (1 + γ) ^ (4 / 3 : ℝ)) * (M : ℝ) ^ (2 / 3 : ℝ) ≤ x} =
      fredholmDet (fun u v =>
        (∫ y in Ioi (0 : ℝ), HnF k M hr γ c ℓ (u + y) * JnF k M hr γ c ℓ (v + y)).re) x := by
  have hγ0 : 0 < γ := by linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hq0, hqpc⟩ := q_facts (M := M) hγ1 ht
  obtain ⟨hpc, -, -, -, -, hL, hR0, hNG, hℓpos, hqℓ, hΓ, -, hSig, hstrict⟩ :=
    bundle k hr γ c (qM γ 1 M) hc hγ1 hq0 hqpc ℓ hℓ_one hℓ_crit hℓ_sub
  have hγsq : γ ^ 2 = (M : ℝ) / N := by rw [hγdef, Real.sq_sqrt (by positivity)]
  have hZ := ZM_ne k M γ (qM γ 1 M) hγ1 hM (piR r hr ℓ) hstrict
  have hσ : 0 < nu γ * (M : ℝ) ^ (1 / 3 : ℝ) := mul_pos (nu_pos hγ0) (by linarith)
  have hs : 0 < nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M := div_pos hσ hMr
  have hsM : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * M = nu γ * (M : ℝ) ^ (1 / 3 : ℝ) :=
    div_mul_cancel₀ _ hMr.ne'
  have hset : {G | (largestEig M U ℓ G - (1 + γ⁻¹) ^ 2) *
        (γ / (1 + γ) ^ (4 / 3 : ℝ)) * (M : ℝ) ^ (2 / 3 : ℝ) ≤ x} =
      {G | largestEig M U ℓ G ≤ mu γ + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * x} := by
    ext G; simp only [Set.mem_setOf_eq]; exact event_iff γ x _ M hγ1 hM
  have hK : ∀ a b : ℝ, nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M *
      kernelKMN M (fun j => (ℓ j)⁻¹) (qM γ 1 M) (cGam γ (qM γ 1 M) c) (rGam γ (qM γ 1 M) c)
        0 (qM γ 1 M / 2) (mu γ + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * a)
        (mu γ + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * b) =
      (∫ y in Ioi (0 : ℝ), HnF k M hr γ c ℓ (a + y) * JnF k M hr γ c ℓ (b + y)).re := by
    intro a b
    rw [(kernelKMN_factorization k M hM hN hr hkr γ (qM γ 1 M) (cGam γ (qM γ 1 M) c) (rGam γ (qM γ 1 M) c)
      0 (qM γ 1 M / 2) a b _ _ hγsq hγ0
      (by rw [add_mul, mul_assoc, mul_comm a, ← mul_assoc, hsM])
      (by rw [add_mul, mul_assoc, mul_comm b, ← mul_assoc, hsM])
      (fun j => (ℓ j)⁻¹) (piR r hr ℓ) (fun j => rfl)
      (fun j hj => by simp only [hℓ_one j hj, inv_one]) hpc hR0 (by linarith)
      (by linarith) hΓ hSig).1]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [HnF, JnF]
    rw [show ∀ Z H J : ℂ, Z * H * (J / Z) = H * (Z * J / Z) from fun Z H J => by ring,
      mul_div_cancel_left₀ _ hZ]
  rw [hset, proposition_2_1 M N hN hNM U ℓ hℓpos (qM γ 1 M) hq0 hqℓ (cGam γ (qM γ 1 M) c)
    (rGam γ (qM γ 1 M) c) hNG hL 0 (qM γ 1 M / 2) (by rw [abs_zero]; linarith) (by linarith) _ hξ]
  unfold fredholmDet
  refine tsum_congr fun n => ?_
  congr 1
  rw [term_affine _ (mu γ) _ x hs]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  congr 1
  ext p q
  simp only [Matrix.of_apply]
  exact hK (w p) (w q)

/-- The limit kernel is the conjugate `e^{-u} K_k(u,v) e^{v}` of the `F_k` kernel. -/
theorem Kinf_eq (k : ℕ) (u v : ℝ) :
    (∫ y in Ioi (0 : ℝ), Hinf 1 k (-1 / 2) (u + y) * Jinf 1 k (-2) (v + y)).re =
      Real.exp (-u) * kernelFk k u v / Real.exp (-v) := by
  have hE : (∫ y in Ioi (0 : ℝ), Hinf 1 k (-1 / 2) (u + y) * Jinf 1 k (-2) (v + y)) -
      (∫ y in Ioi (0 : ℝ),
        ((Real.exp (-1 * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (1 * (v + y)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 k,
        ((Real.exp (-1 * u) * sFn m u * tFn m v * Real.exp (1 * v) : ℝ) : ℂ) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [eq_200_k_zero, sub_self, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    · exact eq_200 k hk 1 one_pos (-1 / 2) (-2) (by norm_num) (by norm_num) (by norm_num) u v
  rw [sub_eq_iff_eq_add] at hE
  rw [hE, Complex.add_re, ← Complex.ofReal_sum, Complex.ofReal_re, integral_complex_ofReal,
    Complex.ofReal_re]
  simp only [neg_mul, one_mul]
  have hint : ∫ y in Ioi (0 : ℝ), Real.exp (-(u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (v + y) =
      Real.exp (-u) * Real.exp v * airyKernel u v := by
    rw [airyKernel, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [add_comm y v, show Real.exp (-(u + y)) = Real.exp (-u) * Real.exp (-y) by
        rw [← Real.exp_add]; congr 1; ring,
      Real.exp_add v y, Real.exp_neg y]
    field_simp
  have hsum : ∑ m ∈ Finset.Icc 1 k, Real.exp (-u) * sFn m u * tFn m v * Real.exp v =
      Real.exp (-u) * Real.exp v * ∑ m ∈ Finset.Icc 1 k, sFn m u * tFn m v := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
  rw [hint, hsum, kernelFk, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  ring

theorem series_limit_eq (k : ℕ) (x : ℝ) :
    fredholmDet (fun u v =>
        (∫ y in Ioi (0 : ℝ), Hinf 1 k (-1 / 2) (u + y) * Jinf 1 k (-2) (v + y)).re) x = F k x := by
  unfold F fredholmDet
  refine tsum_congr fun n => ?_
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [show (Matrix.of fun p q : Fin n =>
      (∫ y in Ioi (0 : ℝ), Hinf 1 k (-1 / 2) (u p + y) * Jinf 1 k (-2) (u q + y)).re) =
      Matrix.of fun p q : Fin n =>
        Real.exp (-(u p)) * kernelFk k (u p) (u q) / Real.exp (-(u q)) from by
    ext p q; simp only [Matrix.of_apply]; exact Kinf_eq k _ _]
  exact det_conj (fun t => Real.exp (-t)) (fun t => (Real.exp_pos _).ne') (kernelFk k) u

end Lib5e

namespace Lib5e

open MeasureTheory Filter Topology Set Complex
open SpikedWishart.SoftEdge

set_option maxHeartbeats 1000000 in
theorem main_R9 (r k : ℕ) (hkr : k ≤ r) (γ₀ c : ℝ) (hγ₀ : 1 ≤ γ₀) (hc : 0 < c)
    (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (γ : ℕ → ℝ) (hγ_def : ∀ n, γ n = Real.sqrt ((M n : ℝ) / (N n : ℝ)))
    (hγ : ∀ n, 1 ≤ γ n ∧ γ n ≤ γ₀) (hr : ∀ n, r ≤ N n)
    (U : ∀ n, Matrix.unitaryGroup (Fin (N n)) ℂ) (ℓ : ∀ n, Fin (N n) → ℝ)
    (hℓ_one : ∀ n (j : Fin (N n)), r ≤ (j : ℕ) → ℓ n j = 1)
    (hℓ_crit : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = 1 + (γ n)⁻¹)
    (hℓ_sub : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < r →
      c ≤ ℓ n j ∧ ℓ n j ≤ 1 + (γ n)⁻¹ - c)
    (x : ℝ) :
    Tendsto (fun n => (sampleLaw (M n) (N n)).real
        {G | (largestEig (M n) (U n) (ℓ n) G - (1 + (γ n)⁻¹) ^ 2) *
            (γ n / (1 + γ n) ^ (4 / 3 : ℝ)) * (M n : ℝ) ^ (2 / 3 : ℝ) ≤ x})
      atTop (𝓝 (F k x)) := by
  -- basic facts on `N n ≤ M n → ∞`
  have hNpos : ∀ n, 0 < N n := by
    intro n
    rcases Nat.eq_zero_or_pos (N n) with h0 | h0
    · have h1 := (hγ n).1
      rw [hγ_def n, h0, Nat.cast_zero, div_zero, Real.sqrt_zero] at h1
      norm_num at h1
    · exact h0
  have hNM : ∀ n, N n ≤ M n := by
    intro n
    have h1 := (hγ n).1
    rw [hγ_def n] at h1
    have hN' : (0 : ℝ) < N n := by exact_mod_cast hNpos n
    have h2 : (1 : ℝ) ≤ (M n : ℝ) / N n := by
      have h3 := one_le_pow₀ (n := 2) h1
      rwa [Real.sq_sqrt (by positivity)] at h3
    rw [one_le_div hN'] at h2
    exact_mod_cast h2
  have hMpos : ∀ n, 0 < M n := fun n => lt_of_lt_of_le (hNpos n) (hNM n)
  have hγsq : ∀ n, γ n ^ 2 = (M n : ℝ) / N n := fun n => by
    rw [hγ_def n, Real.sq_sqrt (by positivity)]
  have hMt : Tendsto (fun n => (M n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono hNM hN)
  have ht : Tendsto (fun n => (M n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hMt
  -- constants
  obtain ⟨hP1, hP2⟩ := proposition_3_1 1 γ₀ c one_pos hγ₀ hc r k hkr
  obtain ⟨C1, c1, M1, hC1, hc1, -, hb1⟩ := hP1 x
  obtain ⟨C2, c2, M2, hC2, hc2, -, hb2⟩ := hP2 x
  obtain ⟨C3, hC3, hb3⟩ := Hinf_bound 1 k (-1 / 2) x (by norm_num)
  obtain ⟨C4, hC4, hb4⟩ := Jinf_bound 1 k (-2) x (by norm_num)
  have hc'0 : 0 < min (min c1 c2) (1 / 2 : ℝ) := lt_min (lt_min hc1 hc2) (by norm_num)
  have hc'1 : min (min c1 c2) (1 / 2 : ℝ) ≤ c1 := (min_le_left _ _).trans (min_le_left _ _)
  have hc'2 : min (min c1 c2) (1 / 2 : ℝ) ≤ c2 := (min_le_left _ _).trans (min_le_right _ _)
  have hc'3 : min (min c1 c2) (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
  have hev : ∀ᶠ n in atTop, M1 ≤ (M n : ℝ) ∧ M2 ≤ (M n : ℝ) ∧
      max 3 ((1 + γ₀) ^ (4 / 3 : ℝ) * |x| + 1) ≤ (M n : ℝ) ^ (1 / 3 : ℝ) :=
    (hMt.eventually_ge_atTop M1).and ((hMt.eventually_ge_atTop M2).and
      (ht.eventually_ge_atTop _))
  have ht3 : ∀ n, max 3 ((1 + γ₀) ^ (4 / 3 : ℝ) * |x| + 1) ≤ (M n : ℝ) ^ (1 / 3 : ℝ) →
      3 ≤ (M n : ℝ) ^ (1 / 3 : ℝ) := fun n h => (le_max_left _ _).trans h
  -- the kernel limit
  have hser := fredholmDet_tendsto_of_factored_kernels
    (fun n => HnF k (M n) (hr n) (γ n) c (ℓ n)) (fun n => JnF k (M n) (hr n) (γ n) c (ℓ n))
    (Hinf 1 k (-1 / 2)) (Jinf 1 k (-2)) (fun n => 1 / (M n : ℝ) ^ (1 / 3 : ℝ))
    ((C1 + C2 + C3 + C4) * Real.exp ((c1 + c2 + 1) * |x|)) (min (min c1 c2) (1 / 2)) x
    (by positivity) hc'0
    (tendsto_const_nhds.div_atTop ht)
    (by
      filter_upwards [hev] with n hn
      have h3 := ht3 n hn.2.2
      exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩)
    (by
      filter_upwards [hev] with n hn w hw
      have h3 := ht3 n hn.2.2
      obtain ⟨hq0, hqpc⟩ := q_facts (M := M n) (hγ n).1 h3
      obtain ⟨hpc, hsub, hpcG, hrG, h1G, hL, -, -, -, -, -, -, -, -⟩ :=
        bundle k (hr n) (γ n) c (qM (γ n) 1 (M n)) hc (hγ n).1 hq0 hqpc (ℓ n) (hℓ_one n)
          (hℓ_crit n) (hℓ_sub n)
      have hb := hb1 (M n) (N n) (γ n) (piR r (hr n) (ℓ n)) _ _ (-1 / 2) w hn.1 (hr n) (hγ_def n)
        (hγ n).1 (hγ n).2 hpc hsub hpcG hrG h1G hL (by norm_num) (by norm_num) hw
      exact hb.trans (bnd_t hC1.le (by linarith) hc'1 (by linarith) hc'0.le hw (by linarith)))
    (by
      filter_upwards [hev] with n hn w hw
      have h3 := ht3 n hn.2.2
      obtain ⟨hq0, hqpc⟩ := q_facts (M := M n) (hγ n).1 h3
      obtain ⟨hpc, hsub, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
        bundle k (hr n) (γ n) c (qM (γ n) 1 (M n)) hc (hγ n).1 hq0 hqpc (ℓ n) (hℓ_one n)
          (hℓ_crit n) (hℓ_sub n)
      have hb := hb2 (M n) (N n) (γ n) (piR r (hr n) (ℓ n)) 0 (qM (γ n) 1 (M n) / 2) (-2) w
        hn.2.1 (hr n) (hγ_def n) (hγ n).1 (hγ n).2 hpc hsub (by rw [abs_zero]; linarith)
        (by linarith) (by norm_num) hw
      exact hb.trans (bnd_t hC2.le (by linarith) hc'2 (by linarith) hc'0.le hw (by linarith)))
    (fun w hw => (hb3 w hw).trans (bnd hC3 (by linarith) (by linarith) (by linarith) hc'0.le hw))
    (fun w hw => by
      have h := hb4 w hw
      rw [show (1 + -2 : ℝ) * w = -1 * w by ring] at h
      exact h.trans (bnd hC4 (by linarith) (by linarith) (by linarith) hc'0.le hw))
    (by
      filter_upwards [hev] with n hn
      have h3 := ht3 n hn.2.2
      obtain ⟨hq0, hqpc⟩ := q_facts (M := M n) (hγ n).1 h3
      obtain ⟨hpc, -, -, -, -, hL, hR0, -, -, -, hΓ, -, hSig, -⟩ :=
        bundle k (hr n) (γ n) c (qM (γ n) 1 (M n)) hc (hγ n).1 hq0 hqpc (ℓ n) (hℓ_one n)
          (hℓ_crit n) (hℓ_sub n)
      exact continuous_const.mul (kernelKMN_factorization k (M n) (hMpos n) (hNpos n) (hr n) hkr (γ n) (qM (γ n) 1 (M n)) _ _
        0 (qM (γ n) 1 (M n) / 2) 0 0 (mu (γ n)) (mu (γ n)) (hγsq n) (by linarith [(hγ n).1])
        (by ring) (by ring) (fun j => (ℓ n j)⁻¹) (piR r (hr n) (ℓ n)) (fun j => rfl)
        (fun j hj => by simp only [hℓ_one n j hj, inv_one]) hpc hR0 (by linarith) (by linarith) hΓ hSig).2.1)
    (by
      filter_upwards [hev] with n hn
      have h3 := ht3 n hn.2.2
      obtain ⟨hq0, hqpc⟩ := q_facts (M := M n) (hγ n).1 h3
      obtain ⟨hpc, -, -, -, -, hL, hR0, -, -, -, hΓ, -, hSig, -⟩ :=
        bundle k (hr n) (γ n) c (qM (γ n) 1 (M n)) hc (hγ n).1 hq0 hqpc (ℓ n) (hℓ_one n)
          (hℓ_crit n) (hℓ_sub n)
      exact (kernelKMN_factorization k (M n) (hMpos n) (hNpos n) (hr n) hkr (γ n) (qM (γ n) 1 (M n)) _ _
        0 (qM (γ n) 1 (M n) / 2) 0 0 (mu (γ n)) (mu (γ n)) (hγsq n) (by linarith [(hγ n).1])
        (by ring) (by ring) (fun j => (ℓ n j)⁻¹) (piR r (hr n) (ℓ n)) (fun j => rfl)
        (fun j hj => by simp only [hℓ_one n j hj, inv_one]) hpc hR0 (by linarith) (by linarith) hΓ hSig).2.2.div_const _)
  rw [series_limit_eq k x] at hser
  refine hser.congr' ?_
  filter_upwards [hev] with n hn
  have h3 := ht3 n hn.2.2
  exact (per_n k (M n) hkr (hr n) (γ n) c x hc (hγ_def n) (hγ n).1 (hNpos n) (hNM n) (U n) (ℓ n)
    (hℓ_one n) (hℓ_crit n) (hℓ_sub n) (hMpos n) h3
    (xi_nonneg (hγ n).1 (hγ n).2 (hMpos n) hn.2.2)).symm

end Lib5e

open SpikedWishart.SoftEdge Filter Topology MeasureTheory in
theorem solution (r k : ℕ) (hkr : k ≤ r) (γ₀ c : ℝ) (hγ₀ : 1 ≤ γ₀) (hc : 0 < c)
    (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (γ : ℕ → ℝ) (hγ_def : ∀ n, γ n = Real.sqrt ((M n : ℝ) / (N n : ℝ)))
    (hγ : ∀ n, 1 ≤ γ n ∧ γ n ≤ γ₀) (hr : ∀ n, r ≤ N n)
    (U : ∀ n, Matrix.unitaryGroup (Fin (N n)) ℂ) (ℓ : ∀ n, Fin (N n) → ℝ)
    (hℓ_one : ∀ n (j : Fin (N n)), r ≤ (j : ℕ) → ℓ n j = 1)
    (hℓ_crit : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = 1 + (γ n)⁻¹)
    (hℓ_sub : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < r →
      c ≤ ℓ n j ∧ ℓ n j ≤ 1 + (γ n)⁻¹ - c)
    (x : ℝ) :
    Tendsto (fun n => (sampleLaw (M n) (N n)).real
        {G | (largestEig (M n) (U n) (ℓ n) G - (1 + (γ n)⁻¹) ^ 2) *
            (γ n / (1 + γ n) ^ (4 / 3 : ℝ)) * (M n : ℝ) ^ (2 / 3 : ℝ) ≤ x})
      atTop (𝓝 (F k x)) := by
  exact Lib5e.main_R9 r k hkr γ₀ c hγ₀ hc M N hN γ hγ_def hγ hr U ℓ hℓ_one hℓ_crit hℓ_sub x
