-- Prove2me | solution 1 for QAlgorithms.Nannicini.gradientAlg_approxLinear
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:08:31.295226+00:00
-- url     : https://prove2.me/submissions/a9ad6f3d-88a6-4847-8648-0a99a30641d5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false

open scoped Matrix BigOperators ComplexConjugate
open QAlgorithms QAlgorithms.Nannicini

noncomputable section

/-! ### Part 1: Real trigonometric and polynomial inequalities -/

private lemma pi_sq_lt : Real.pi ^ 2 < 987 / 100 := by
  have h1 : 0 < Real.pi := Real.pi_pos
  have h2 : Real.pi < 3.1416 := Real.pi_lt_d4
  nlinarith

private lemma one_sub_sq_div_two_le_cos_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t => Real.cos t - (1 - t ^ 2 / 2)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt f (-Real.sin t + t) t := by
    intro t _
    have h1 := Real.hasDerivAt_cos t
    have h2 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2) (-t) t := by
      have hpow := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
      have hsub := (hasDerivAt_const t (1 : ℝ)).sub hpow
      have heq : (0 : ℝ) - (2 : ℕ) * t ^ (2 - 1) / 2 = -t := by ring
      rwa [heq] at hsub
    have h3 := h1.sub h2
    rwa [sub_neg_eq_add] at h3
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have hsin := Real.sin_le ht0
      linarith
  have h0 : f 0 ≤ f x := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [f, Real.cos_zero] at h0
  linarith

private lemma one_sub_sq_div_two_le_cos (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x := by
  rcases le_total 0 x with hx | hx
  · exact one_sub_sq_div_two_le_cos_nonneg hx
  · have h := one_sub_sq_div_two_le_cos_nonneg (neg_nonneg.mpr hx)
    rw [Real.cos_neg, neg_sq] at h
    exact h

private lemma sub_cube_div_six_le_sin {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  let g : ℝ → ℝ := fun t => Real.sin t - (t - t ^ 3 / 6)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt g (Real.cos t - (1 - t ^ 2 / 2)) t := by
    intro t _
    have h1 := Real.hasDerivAt_sin t
    have h2 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6) (1 - t ^ 2 / 2) t := by
      have hpow := (hasDerivAt_pow 3 t).div_const (6 : ℝ)
      have hsub := (hasDerivAt_id t).sub hpow
      have heq : (1 : ℝ) - (3 : ℕ) * t ^ (3 - 1) / 6 = 1 - t ^ 2 / 2 := by ring
      rwa [heq] at hsub
    exact h1.sub h2
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t _
      have hcos := one_sub_sq_div_two_le_cos t
      linarith
  have h0 : g 0 ≤ g x := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [g, Real.sin_zero] at h0
  linarith

private lemma sin_pi_ge_of_quarter {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) :
    Real.pi * a * (2871 / 3200) ≤ Real.sin (Real.pi * a) := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hx : 0 ≤ Real.pi * a := mul_nonneg hpi ha0
  have hsin := sub_cube_div_six_le_sin hx
  have hpi2 := pi_sq_lt
  have ha2 : a ^ 2 ≤ 1 / 16 := by nlinarith
  have h1 : Real.pi ^ 2 * a ^ 2 ≤ (987 / 100) * (1 / 16) := by nlinarith
  have h2 : Real.pi * a * (2871 / 3200) ≤ Real.pi * a - (Real.pi * a) ^ 3 / 6 := by
    have : Real.pi * a - (Real.pi * a) ^ 3 / 6 - Real.pi * a * (2871 / 3200) =
        (Real.pi * a / 6) * (987 / 1600 - Real.pi ^ 2 * a ^ 2) := by ring
    nlinarith
  linarith

private lemma two_point_sin_bound {a : ℝ} (ha1 : 1 / 4 ≤ a) (ha2 : a ≤ 3 / 4) :
    803 / 1000 <
      Real.sin (Real.pi * a) ^ 2 / (Real.pi * a) ^ 2 +
        Real.sin (Real.pi * (1 - a)) ^ 2 / (Real.pi * (1 - a)) ^ 2 := by
  have hsym : Real.sin (Real.pi * (1 - a)) = Real.sin (Real.pi * a) := by
    rw [show Real.pi * (1 - a) = Real.pi - Real.pi * a by ring, Real.sin_pi_sub]
  rw [hsym]
  have hcos_eq : Real.sin (Real.pi * a) = Real.cos ((Real.pi / 2) * (1 - 2 * a)) := by
    rw [show (Real.pi / 2) * (1 - 2 * a) = Real.pi / 2 - Real.pi * a by ring,
      Real.cos_pi_div_two_sub]
  let w : ℝ := (1 - 2 * a) ^ 2
  have hw0 : 0 ≤ w := sq_nonneg (1 - 2 * a)
  have hw1 : w ≤ 1 / 4 := by
    dsimp [w]
    nlinarith
  have hpi2 := pi_sq_lt
  have hcos : 1 - (987 / 800) * w ≤ Real.sin (Real.pi * a) := by
    rw [hcos_eq]
    have h1 := one_sub_sq_div_two_le_cos ((Real.pi / 2) * (1 - 2 * a))
    have h2 : ((Real.pi / 2) * (1 - 2 * a)) ^ 2 / 2 = (Real.pi ^ 2 / 8) * w := by
      dsimp [w]; ring
    rw [h2] at h1
    nlinarith
  have hcos_pos : 0 ≤ 1 - (987 / 800) * w := by linarith
  have hsin_sq : (1 - (987 / 800) * w) ^ 2 ≤ Real.sin (Real.pi * a) ^ 2 := by
    nlinarith
  have ha_pos : 0 < a := by linarith
  have h1a_pos : 0 < 1 - a := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hcomb :
      Real.sin (Real.pi * a) ^ 2 / (Real.pi * a) ^ 2 +
        Real.sin (Real.pi * a) ^ 2 / (Real.pi * (1 - a)) ^ 2 =
      Real.sin (Real.pi * a) ^ 2 * ((1 - a) ^ 2 + a ^ 2) / (Real.pi ^ 2 * (a * (1 - a)) ^ 2) := by
    field_simp
  rw [hcomb]
  have hid1 : (1 - a) ^ 2 + a ^ 2 = (1 + w) / 2 := by dsimp [w]; ring
  have hid2 : a * (1 - a) = (1 - w) / 4 := by dsimp [w]; ring
  rw [hid1, hid2]
  have h1w_pos : 0 < 1 - w := by linarith
  have hdenom_pos : 0 < Real.pi ^ 2 * ((1 - w) / 4) ^ 2 := by positivity
  rw [lt_div_iff₀ hdenom_pos]
  have hQ : (803 / 1000) * ((987 / 100) * ((1 - w) / 4) ^ 2) <
      (1 - (987 / 800) * w) ^ 2 * ((1 + w) / 2) := by
    have hident :
        (1 - (987 / 800) * w) ^ 2 * ((1 + w) / 2) -
          (803 / 1000) * ((987 / 100) * ((1 - w) / 4) ^ 2) =
        7439 / 1600000 +
        (382553 / 25600000) * w +
        (6195399 / 6400000) * (w * (1 / 4 - w)) +
        (974169 / 1280000) * (w * w ^ 2) := by ring
    have hw_sub : 0 ≤ 1 / 4 - w := by linarith
    have hprod1 : 0 ≤ w * (1 / 4 - w) := mul_nonneg hw0 hw_sub
    have hprod2 : 0 ≤ w * w ^ 2 := mul_nonneg hw0 (sq_nonneg w)
    linarith
  have hnum_le :
      (1 - (987 / 800) * w) ^ 2 * ((1 + w) / 2) ≤ Real.sin (Real.pi * a) ^ 2 * ((1 + w) / 2) := by
    nlinarith
  have hden_lt :
      Real.pi ^ 2 * ((1 - w) / 4) ^ 2 < (987 / 100) * ((1 - w) / 4) ^ 2 := by
    have : 0 < ((1 - w) / 4) ^ 2 := by positivity
    nlinarith
  nlinarith

/-! ### Part 2: Complex exponential norm identities -/

private lemma norm_exp_two_pi_I_mul (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

private lemma norm_exp_I_sub_one_sq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
    Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im,
    mul_one, sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.cos_ofReal_im, Complex.mul_im, zero_add, Complex.one_im]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (θ / 2)
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h1
    linarith
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h1 := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h1
    exact h1
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  calc
    (Real.cos θ - 1) * (Real.cos θ - 1) + Real.sin θ * Real.sin θ
      = (Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2) * (4 * Real.sin (θ / 2) ^ 2) := by
        rw [hcos, hsin]; ring
    _ = 4 * Real.sin (θ / 2) ^ 2 := by rw [h2, one_mul]

private lemma norm_exp_two_pi_I_sub_one (δ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
  have hsq : ‖Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) - 1‖ ^ 2 =
      (2 * |Real.sin (Real.pi * δ)|) ^ 2 := by
    rw [show (2 * Real.pi * Complex.I * (δ : ℂ)) = ((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [norm_exp_I_sub_one_sq (2 * Real.pi * δ)]
    rw [show 2 * Real.pi * δ / 2 = Real.pi * δ by ring, mul_pow, sq_abs]
    ring
  have h1 : 0 ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ)) - 1‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * δ)| := by positivity
  nlinarith [sq_eq_sq_iff_eq_or_eq_neg.mp hsq]

private lemma norm_exp_sub_exp_sq_le (u v : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))‖ ^ 2 ≤
      (2 * Real.pi * |u - v|) ^ 2 := by
  have hfac :
      Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) -
        Complex.exp (2 * Real.pi * Complex.I * (v : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ)) *
        (Complex.exp (2 * Real.pi * Complex.I * ((u - v : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfac, norm_mul, norm_exp_two_pi_I_mul v, one_mul, norm_exp_two_pi_I_sub_one (u - v)]
  have hsin : |Real.sin (Real.pi * (u - v))| ≤ |Real.pi * (u - v)| := Real.abs_sin_le_abs
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have h0 : 0 ≤ 2 * |Real.sin (Real.pi * (u - v))| := by positivity
  nlinarith

private lemma norm_exp_sub_exp_sq_le_four (u v : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))‖ ^ 2 ≤ 4 := by
  have htri :
      ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) -
        Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))‖ ≤ 2 := by
    calc
      ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) -
          Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))‖
        ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ))‖ +
            ‖Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_exp_two_pi_I_mul, norm_exp_two_pi_I_mul]
      _ = 2 := by norm_num
  have h0 : 0 ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ))‖ := norm_nonneg _
  nlinarith

/-! ### Part 3: Grid exponential sum `gridSum` and unitarity of `gridQFT` and `piKron` -/

private lemma star_exp_two_pi_I_mul (x : ℝ) :
    star (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) := by
  have h1 : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) = -(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, h2]
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma star_gridQFT_apply (q : ℕ) (j y : Qubits q) :
    (star (gridQFT q)) j y =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q j) : ℝ) : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ) := by
  change star (gridQFT q y j) = _
  simp only [gridQFT, Matrix.of_apply, star_mul']
  have h1 : (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (gridPoint q y : ℂ) * (gridPoint q j : ℂ)) =
      2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * gridPoint q y * gridPoint q j : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, star_exp_two_pi_I_mul]
  have h2 : star (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)) = ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ) := by
    rw [← Complex.ofReal_inv]
    exact Complex.conj_ofReal _
  rw [h2, mul_comm]

private lemma bitsToNat_symm (q : ℕ) (r : Fin (2 ^ q)) :
    bitsToNat ((bitsEquivFin q).symm r) = (r : ℕ) := by
  have h := bitsEquivFin_apply ((bitsEquivFin q).symm r)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private lemma gridPoint_symm (q : ℕ) (r : Fin (2 ^ q)) :
    gridPoint q ((bitsEquivFin q).symm r) =
      ((r : ℕ) : ℝ) * ((2 : ℝ) ^ q)⁻¹ + (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) := by
  simp only [gridPoint, bitsToNat_symm]
  ring

private lemma sqrt_two_pow_inv_mul_self (q : ℕ) :
    (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ) * ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)) =
      (((2 : ℝ) ^ q)⁻¹ : ℂ) := by
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  have hreal : (Real.sqrt ((2 : ℝ) ^ q))⁻¹ * (Real.sqrt ((2 : ℝ) ^ q))⁻¹ = ((2 : ℝ) ^ q)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hpos]
  exact_mod_cast hreal

private noncomputable def gridSum (q : ℕ) (δ : ℝ) : ℂ :=
  (∑ y : Qubits q,
    Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * δ * gridPoint q y : ℝ) : ℂ))) *
    (((2 : ℝ) ^ q)⁻¹ : ℂ)

private lemma gridSum_zero (q : ℕ) : gridSum q 0 = 1 := by
  simp only [gridSum, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul, mul_one]
  have h2q : ((2 : ℂ) ^ q) ≠ 0 := pow_ne_zero q (by norm_num)
  push_cast
  exact mul_inv_cancel₀ h2q

private lemma sum_qubits_exp_gridPoint (q : ℕ) (δ : ℝ) :
    (∑ y : Qubits q,
      Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * δ * gridPoint q y : ℝ) : ℂ))) =
    Complex.exp (2 * Real.pi * Complex.I *
      (((2 : ℝ) ^ q * δ * (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) : ℝ) : ℂ)) *
      ∑ r ∈ Finset.range (2 ^ q), (Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ))) ^ r := by
  rw [← (bitsEquivFin q).symm.sum_comp]
  have hterm : ∀ r : Fin (2 ^ q),
      Complex.exp (2 * Real.pi * Complex.I *
        (((2 : ℝ) ^ q * δ * gridPoint q ((bitsEquivFin q).symm r) : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((2 : ℝ) ^ q * δ * (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) : ℝ) : ℂ)) *
        (Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ))) ^ (r : ℕ) := by
    intro r
    have h2q : (2 : ℝ) ^ q ≠ 0 := pow_ne_zero q (by norm_num)
    rw [gridPoint_symm, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hmul :
        (2 : ℝ) ^ q * δ * (((r : ℕ) : ℝ) * ((2 : ℝ) ^ q)⁻¹ + (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹)) =
        (2 : ℝ) ^ q * δ * (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) + (r : ℕ) * δ := by
      calc
        (2 : ℝ) ^ q * δ * (((r : ℕ) : ℝ) * ((2 : ℝ) ^ q)⁻¹ + (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹))
          = (2 : ℝ) ^ q * δ * (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) +
              ((2 : ℝ) ^ q * ((2 : ℝ) ^ q)⁻¹) * ((r : ℕ) * δ) := by ring
        _ = (2 : ℝ) ^ q * δ * (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) + (r : ℕ) * δ := by
          rw [mul_inv_cancel₀ h2q, one_mul]
    rw [hmul]
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun n : ℕ => (Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ))) ^ n) (2 ^ q)

private lemma norm_gridSum_mul_sin (q : ℕ) (δ : ℝ) :
    ‖gridSum q δ‖ * ((2 : ℝ) ^ q * |Real.sin (Real.pi * δ)|) =
      |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * (δ : ℂ))
  let φ : ℂ := Complex.exp (2 * Real.pi * Complex.I *
    (((2 : ℝ) ^ q * δ * (-2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹) : ℝ) : ℂ))
  have hgeom : (∑ r ∈ Finset.range (2 ^ q), ω ^ r) * (ω - 1) = ω ^ (2 ^ q) - 1 :=
    geom_sum_mul ω (2 ^ q)
  have hpow : ω ^ (2 ^ q) = Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * δ : ℝ) : ℂ)) := by
    dsimp [ω]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hid : gridSum q δ * (ω - 1) = φ * (ω ^ (2 ^ q) - 1) * (((2 : ℝ) ^ q)⁻¹ : ℂ) := by
    dsimp [gridSum, φ]
    rw [sum_qubits_exp_gridPoint q δ]
    calc
      (φ * ∑ r ∈ Finset.range (2 ^ q), ω ^ r) * (((2 : ℝ) ^ q)⁻¹ : ℂ) * (ω - 1)
        = φ * ((∑ r ∈ Finset.range (2 ^ q), ω ^ r) * (ω - 1)) * (((2 : ℝ) ^ q)⁻¹ : ℂ) := by ring
      _ = φ * (ω ^ (2 ^ q) - 1) * (((2 : ℝ) ^ q)⁻¹ : ℂ) := by rw [hgeom]
  have hnorm := congrArg Norm.norm hid
  rw [norm_mul, norm_mul, norm_mul] at hnorm
  have hφ : ‖φ‖ = 1 := norm_exp_two_pi_I_mul _
  have hω1 : ‖ω - 1‖ = 2 * |Real.sin (Real.pi * δ)| := norm_exp_two_pi_I_sub_one δ
  have hω2 : ‖ω ^ (2 ^ q) - 1‖ = 2 * |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| := by
    rw [hpow]
    exact norm_exp_two_pi_I_sub_one ((2 : ℝ) ^ q * δ)
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have h2q_norm : ‖(((2 : ℝ) ^ q)⁻¹ : ℂ)‖ = ((2 : ℝ) ^ q)⁻¹ := by simp
  rw [hφ, one_mul, hω1, hω2, h2q_norm] at hnorm
  have h2q_ne : (2 : ℝ) ^ q ≠ 0 := h2q_pos.ne'
  calc
    ‖gridSum q δ‖ * ((2 : ℝ) ^ q * |Real.sin (Real.pi * δ)|)
      = (‖gridSum q δ‖ * (2 * |Real.sin (Real.pi * δ)|)) * ((2 : ℝ) ^ q / 2) := by ring
    _ = (2 * |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| * ((2 : ℝ) ^ q)⁻¹) * ((2 : ℝ) ^ q / 2) := by
        rw [hnorm]
    _ = |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| * ((2 : ℝ) ^ q * ((2 : ℝ) ^ q)⁻¹) := by ring
    _ = |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| := by rw [mul_inv_cancel₀ h2q_ne, mul_one]

private lemma star_gridQFT_mul_self_apply (q : ℕ) (j k : Qubits q) :
    (star (gridQFT q) * gridQFT q) j k = gridSum q (gridPoint q k - gridPoint q j) := by
  rw [Matrix.mul_apply, gridSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [star_gridQFT_apply, gridQFT, Matrix.of_apply]
  have hexp :
      Complex.exp (2 * Real.pi * Complex.I *
        ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q j) : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (gridPoint q y : ℂ) * (gridPoint q k : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((2 : ℝ) ^ q * (gridPoint q k - gridPoint q j) * gridPoint q y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (Complex.exp (2 * Real.pi * Complex.I *
        ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q j) : ℝ) : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)) *
      (Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (gridPoint q y : ℂ) * (gridPoint q k : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ))
      = (Complex.exp (2 * Real.pi * Complex.I *
          ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q j) : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (gridPoint q y : ℂ) * (gridPoint q k : ℂ))) *
        (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ) * ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)) := by ring
    _ = Complex.exp (2 * Real.pi * Complex.I *
          (((2 : ℝ) ^ q * (gridPoint q k - gridPoint q j) * gridPoint q y : ℝ) : ℂ)) *
        (((2 : ℝ) ^ q)⁻¹ : ℂ) := by rw [hexp, sqrt_two_pow_inv_mul_self]

private lemma star_gridQFT_mul_self (q : ℕ) : star (gridQFT q) * gridQFT q = 1 := by
  ext j k
  rw [star_gridQFT_mul_self_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [sub_self, gridSum_zero, if_pos rfl]
  · rw [if_neg hjk]
    let δ : ℝ := gridPoint q k - gridPoint q j
    let m : ℤ := (bitsToNat k : ℤ) - (bitsToNat j : ℤ)
    have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
    have h2q_ne : (2 : ℝ) ^ q ≠ 0 := h2q_pos.ne'
    have hδ_eq : δ = (m : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
      dsimp [δ, m, gridPoint]
      push_cast
      ring
    have h2qδ : (2 : ℝ) ^ q * δ = (m : ℝ) := by
      rw [hδ_eq]
      calc
        (2 : ℝ) ^ q * ((m : ℝ) * ((2 : ℝ) ^ q)⁻¹) = (m : ℝ) * ((2 : ℝ) ^ q * ((2 : ℝ) ^ q)⁻¹) := by ring
        _ = (m : ℝ) := by rw [mul_inv_cancel₀ h2q_ne, mul_one]
    have hm_ne : m ≠ 0 := by
      intro hm0
      have hnat : bitsToNat k = bitsToNat j := by omega
      have hfin : bitsEquivFin q k = bitsEquivFin q j := by
        apply Fin.ext
        rw [bitsEquivFin_apply, bitsEquivFin_apply, hnat]
      exact hjk ((bitsEquivFin q).injective hfin).symm
    have hm_abs_ge : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
      exact_mod_cast this
    have hk_lt : (bitsToNat k : ℝ) < (2 : ℝ) ^ q := by
      have h := (bitsEquivFin q k).isLt
      rw [bitsEquivFin_apply] at h
      exact_mod_cast h
    have hj_lt : (bitsToNat j : ℝ) < (2 : ℝ) ^ q := by
      have h := (bitsEquivFin q j).isLt
      rw [bitsEquivFin_apply] at h
      exact_mod_cast h
    have hk_nonneg : (0 : ℝ) ≤ (bitsToNat k : ℝ) := Nat.cast_nonneg _
    have hj_nonneg : (0 : ℝ) ≤ (bitsToNat j : ℝ) := Nat.cast_nonneg _
    have hm_abs_lt : |(m : ℝ)| < (2 : ℝ) ^ q := by
      have : (m : ℝ) = (bitsToNat k : ℝ) - (bitsToNat j : ℝ) := by dsimp [m]; push_cast; rfl
      rw [this, abs_lt]
      constructor <;> linarith
    have hδ_pos : 0 < |δ| := by
      rw [hδ_eq, abs_mul, abs_of_pos (inv_pos.mpr h2q_pos)]
      exact mul_pos (by linarith) (inv_pos.mpr h2q_pos)
    have hδ_lt_one : |δ| < 1 := by
      rw [hδ_eq, abs_mul, abs_of_pos (inv_pos.mpr h2q_pos)]
      calc
        |(m : ℝ)| * ((2 : ℝ) ^ q)⁻¹ < (2 : ℝ) ^ q * ((2 : ℝ) ^ q)⁻¹ :=
          mul_lt_mul_of_pos_right hm_abs_lt (inv_pos.mpr h2q_pos)
        _ = 1 := mul_inv_cancel₀ h2q_ne
    have hsin_pos : 0 < |Real.sin (Real.pi * δ)| := by
      have h1 : |Real.sin (Real.pi * δ)| = Real.sin (Real.pi * |δ|) := by
        rcases le_total 0 δ with h0 | h0
        · rw [abs_of_nonneg h0]
          exact abs_of_pos (Real.sin_pos_of_pos_of_lt_pi
            (mul_pos Real.pi_pos (by rwa [abs_of_nonneg h0] at hδ_pos))
            (by nlinarith [Real.pi_pos, show δ < 1 by rwa [abs_of_nonneg h0] at hδ_lt_one]))
        · have hneg : Real.pi * δ = -(Real.pi * (-δ)) := by ring
          rw [abs_of_nonpos h0, hneg, Real.sin_neg, abs_neg]
          exact abs_of_pos (Real.sin_pos_of_pos_of_lt_pi
            (mul_pos Real.pi_pos (by linarith [abs_of_nonpos h0]))
            (by nlinarith [Real.pi_pos, abs_of_nonpos h0]))
      rw [h1]
      exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hδ_pos)
        (by nlinarith [Real.pi_pos])
    have hsin_rhs : |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| = 0 := by
      rw [h2qδ, show Real.pi * (m : ℝ) = (m : ℝ) * Real.pi by ring, Real.sin_int_mul_pi, abs_zero]
    have hident := norm_gridSum_mul_sin q δ
    rw [hsin_rhs] at hident
    have hfac_pos : 0 < (2 : ℝ) ^ q * |Real.sin (Real.pi * δ)| := mul_pos h2q_pos hsin_pos
    have hnorm0 : ‖gridSum q δ‖ = 0 := by nlinarith
    exact norm_eq_zero.mp hnorm0

private lemma star_gridQFT_mem_unitaryGroup (q : ℕ) :
    star (gridQFT q) ∈ Matrix.unitaryGroup (Qubits q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [star_star]
  exact star_gridQFT_mul_self q

private lemma piKron_one {ι : Type*} [DecidableEq ι] (d : ℕ) :
    piKron d (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp [piKron, Matrix.one_apply, Finset.prod_boole, funext_iff]

private lemma piKron_mul {ι : Type*} [Fintype ι] (d : ℕ) (A B : Matrix ι ι ℂ) :
    piKron d A * piKron d B = piKron d (A * B) := by
  ext x z
  simp only [piKron, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i y => A (x i) y * B y (z i))).symm

private lemma piKron_star {ι : Type*} (d : ℕ) (M : Matrix ι ι ℂ) :
    star (piKron d M) = piKron d (star M) := by
  ext x y
  simp only [piKron, Matrix.star_apply, Matrix.of_apply, star_prod]

private lemma piKron_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    piKron d U ∈ Matrix.unitaryGroup (Fin d → ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  rw [piKron_star, piKron_mul, hU, piKron_one]

/-! ### Part 4: State distance bound between `f` and the linear function `l` -/

private noncomputable def phaseState (d q : ℕ) (f : (Fin d → ℝ) → ℝ) :
    EuclideanSpace ℂ (Fin d → Qubits q) :=
  act (Matrix.diagonal fun x : Fin d → Qubits q =>
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (f fun i => gridPoint q (x i) : ℂ)))
    (act (piKron d (hadamardN q)) (ket fun _ _ => false))

private lemma gradientAlgState_eq_act_phaseState (d q : ℕ) (f : (Fin d → ℝ) → ℝ) :
    gradientAlgState d q f = act (piKron d (star (gridQFT q))) (phaseState d q f) := rfl

private lemma act_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (ψ φ : EuclideanSpace ℂ ι) :
    act A ψ - act A φ = act A (ψ - φ) := by
  ext x
  change (Matrix.mulVec A (WithLp.ofLp ψ)) x - (Matrix.mulVec A (WithLp.ofLp φ)) x =
    (Matrix.mulVec A (WithLp.ofLp (ψ - φ))) x
  rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
  rfl

private lemma sqrt_two_inv_pow (q : ℕ) :
    (Real.sqrt 2)⁻¹ ^ q = (Real.sqrt ((2 : ℝ) ^ q))⁻¹ := by
  rw [inv_pow]
  congr 1
  have h1 : (Real.sqrt 2 ^ q) ^ 2 = (2 : ℝ) ^ q := by
    rw [← pow_mul, mul_comm q 2, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [← h1, Real.sqrt_sq (by positivity)]

private lemma hadamardN_false_Right (q : ℕ) (y : Qubits q) :
    hadamardN q y (fun _ => false) = (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ) := by
  have hdot : dotBits (fun _ : Fin q => false) y = false := by
    unfold dotBits
    exact Finset.sum_eq_zero (fun _ _ => rfl)
  rw [hadamardN, Matrix.of_apply, if_neg (by rw [hdot]; decide), sqrt_two_inv_pow]

private lemma phaseState_apply (d q : ℕ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → Qubits q) :
    phaseState d q f x =
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (f (fun i => gridPoint q (x i)) : ℂ)) *
        ∏ _i : Fin d, (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ) := by
  dsimp [phaseState]
  change (Matrix.mulVec (Matrix.diagonal _) (WithLp.ofLp (act (piKron d (hadamardN q)) (ket fun _ _ => false)))) x = _
  rw [Matrix.mulVec_diagonal]
  congr 1
  change (Matrix.mulVec (piKron d (hadamardN q)) (WithLp.ofLp (ket fun _ _ => false))) x = _
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (fun _ _ => false)]
  · have hket : (ket (fun _ : Fin d => fun _ : Fin q => false)) (fun _ _ => false) = 1 := by
      simp [ket]
    rw [hket, mul_one]
    simp only [piKron, Matrix.of_apply, hadamardN_false_Right]
  · intro y _ hy
    have hket : (ket (fun _ : Fin d => fun _ : Fin q => false)) y = 0 := by
      simp [ket, hy]
    rw [hket, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private lemma norm_prod_sqrt_two_pow_inv_sq (d q : ℕ) :
    ‖(∏ _i : Fin d, (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ))‖ ^ 2 = ((2 : ℝ) ^ (d * q))⁻¹ := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow]
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  have hnorm : ‖(((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt ((2 : ℝ) ^ q))⁻¹ := by
    exact Complex.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [hnorm, ← pow_mul, mul_comm d 2, pow_mul, inv_pow, Real.sq_sqrt hpos, ← inv_pow, ← pow_mul,
    mul_comm q d, inv_pow]

private lemma norm_gradientAlgState_sub_le (d q : ℕ) (b : ℝ) (g : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ)
    (hf : (999 / 1000 : ℝ) * (2 : ℝ) ^ (d * q) ≤
      ((Finset.univ.filter fun x : Fin d → Qubits q =>
          |f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b| ≤
            1 / (20 * Real.pi * (2 : ℝ) ^ q)).card : ℝ)) :
    ‖gradientAlgState d q f - gradientAlgState d q (fun z => ∑ i, g i * z i + b)‖ ≤ 119 / 1000 := by
  let l : (Fin d → ℝ) → ℝ := fun z => ∑ i, g i * z i + b
  have hU : piKron d (star (gridQFT q)) ∈ Matrix.unitaryGroup (Fin d → Qubits q) ℂ :=
    piKron_mem_unitaryGroup d (star_gridQFT_mem_unitaryGroup q)
  have hnorm_eq :
      ‖gradientAlgState d q f - gradientAlgState d q l‖ = ‖phaseState d q f - phaseState d q l‖ := by
    rw [gradientAlgState_eq_act_phaseState, gradientAlgState_eq_act_phaseState, act_sub]
    exact act_norm_of_mem_unitaryGroup hU (phaseState d q f - phaseState d q l)
  rw [hnorm_eq]
  have hsq :
      ‖phaseState d q f - phaseState d q l‖ ^ 2 =
        ((2 : ℝ) ^ (d * q))⁻¹ *
          ∑ x : Fin d → Qubits q,
            ‖Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * f (fun i => gridPoint q (x i)) : ℝ) : ℂ)) -
              Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * l (fun i => gridPoint q (x i)) : ℝ) : ℂ))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    change ‖phaseState d q f x - phaseState d q l x‖ ^ 2 = _
    rw [phaseState_apply, phaseState_apply, ← sub_mul, norm_mul, mul_pow,
      norm_prod_sqrt_two_pow_inv_sq, mul_comm]
    congr 2
    have h1 : (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (f (fun i => gridPoint q (x i)) : ℂ)) =
        2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * f (fun i => gridPoint q (x i)) : ℝ) : ℂ) := by
      push_cast; ring
    have h2 : (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (l (fun i => gridPoint q (x i)) : ℂ)) =
        2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * l (fun i => gridPoint q (x i)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, h2]
  let P : (Fin d → Qubits q) → Prop := fun x =>
    |f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b| ≤
      1 / (20 * Real.pi * (2 : ℝ) ^ q)
  let term : (Fin d → Qubits q) → ℝ := fun x =>
    ‖Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * f (fun i => gridPoint q (x i)) : ℝ) : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * l (fun i => gridPoint q (x i)) : ℝ) : ℂ))‖ ^ 2
  have hsplit : (∑ x : Fin d → Qubits q, term x) =
      (∑ x ∈ Finset.univ.filter P, term x) + (∑ x ∈ Finset.univ.filter (fun x => ¬ P x), term x) := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ P term).symm
  have hgood_term : ∀ x ∈ Finset.univ.filter P, term x ≤ 1 / 100 := by
    intro x hx
    have hxP : P x := (Finset.mem_filter.mp hx).2
    have hle := norm_exp_sub_exp_sq_le
      ((2 : ℝ) ^ q * f (fun i => gridPoint q (x i)))
      ((2 : ℝ) ^ q * l (fun i => gridPoint q (x i)))
    have hdiff :
        (2 : ℝ) ^ q * f (fun i => gridPoint q (x i)) -
          (2 : ℝ) ^ q * l (fun i => gridPoint q (x i)) =
        (2 : ℝ) ^ q * (f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b) := by
      dsimp [l]; ring
    have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
    have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    have habs :
        2 * Real.pi * |(2 : ℝ) ^ q * f (fun i => gridPoint q (x i)) -
          (2 : ℝ) ^ q * l (fun i => gridPoint q (x i))| ≤ 1 / 10 := by
      rw [hdiff, abs_mul, abs_of_pos h2q_pos]
      have hmul :
          2 * Real.pi * ((2 : ℝ) ^ q * |f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b|) ≤
          2 * Real.pi * ((2 : ℝ) ^ q * (1 / (20 * Real.pi * (2 : ℝ) ^ q))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxP h2q_pos.le) (by positivity)
      have hsimp : 2 * Real.pi * ((2 : ℝ) ^ q * (1 / (20 * Real.pi * (2 : ℝ) ^ q))) = 1 / 10 := by
        field_simp
        ring
      linarith
    have h0 : 0 ≤ 2 * Real.pi * |(2 : ℝ) ^ q * f (fun i => gridPoint q (x i)) -
        (2 : ℝ) ^ q * l (fun i => gridPoint q (x i))| := by positivity
    dsimp [term]
    nlinarith
  have hbad_term : ∀ x ∈ Finset.univ.filter (fun x => ¬ P x), term x ≤ 4 := by
    intro x _
    exact norm_exp_sub_exp_sq_le_four _ _
  have hgood_sum :
      (∑ x ∈ Finset.univ.filter P, term x) ≤ ((Finset.univ.filter P).card : ℝ) * (1 / 100) := by
    calc
      (∑ x ∈ Finset.univ.filter P, term x) ≤ ∑ _x ∈ Finset.univ.filter P, (1 / 100 : ℝ) :=
        Finset.sum_le_sum hgood_term
      _ = ((Finset.univ.filter P).card : ℝ) * (1 / 100) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hbad_sum :
      (∑ x ∈ Finset.univ.filter (fun x => ¬ P x), term x) ≤
        ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) * 4 := by
    calc
      (∑ x ∈ Finset.univ.filter (fun x => ¬ P x), term x) ≤
          ∑ _x ∈ Finset.univ.filter (fun x => ¬ P x), (4 : ℝ) :=
        Finset.sum_le_sum hbad_term
      _ = ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) * 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_univ : ((Finset.univ : Finset (Fin d → Qubits q)).card : ℝ) = (2 : ℝ) ^ (d * q) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_bool, ← pow_mul, mul_comm q d]
    push_cast
    rfl
  have hcard_add :
      ((Finset.univ.filter P).card : ℝ) + ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) =
        (2 : ℝ) ^ (d * q) := by
    have hsum1 := Finset.sum_filter_add_sum_filter_not (s := Finset.univ) P (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum1
    linarith
  have hgood_card_le : ((Finset.univ.filter P).card : ℝ) ≤ (2 : ℝ) ^ (d * q) := by
    have : 0 ≤ ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hbad_card_le : ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) ≤ (1 / 1000) * (2 : ℝ) ^ (d * q) := by
    linarith
  have h2dq_pos : (0 : ℝ) < (2 : ℝ) ^ (d * q) := by positivity
  have hsq_le : ‖phaseState d q f - phaseState d q l‖ ^ 2 ≤ (119 / 1000) ^ 2 := by
    rw [hsq]
    change ((2 : ℝ) ^ (d * q))⁻¹ * (∑ x : Fin d → Qubits q, term x) ≤ (119 / 1000) ^ 2
    rw [hsplit]
    have hsum_le :
        (∑ x ∈ Finset.univ.filter P, term x) + (∑ x ∈ Finset.univ.filter (fun x => ¬ P x), term x) ≤
          (14 / 1000) * (2 : ℝ) ^ (d * q) := by
      linarith
    have hinv_nonneg : 0 ≤ ((2 : ℝ) ^ (d * q))⁻¹ := inv_nonneg.mpr h2dq_pos.le
    calc
      ((2 : ℝ) ^ (d * q))⁻¹ *
          ((∑ x ∈ Finset.univ.filter P, term x) + (∑ x ∈ Finset.univ.filter (fun x => ¬ P x), term x))
        ≤ ((2 : ℝ) ^ (d * q))⁻¹ * ((14 / 1000) * (2 : ℝ) ^ (d * q)) :=
          mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
      _ = 14 / 1000 := by
          rw [← mul_assoc, mul_comm (((2 : ℝ) ^ (d * q))⁻¹), mul_assoc,
            inv_mul_cancel₀ h2dq_pos.ne', mul_one]
      _ ≤ (119 / 1000) ^ 2 := by norm_num
  have hnorm_nonneg : 0 ≤ ‖phaseState d q f - phaseState d q l‖ := norm_nonneg _
  nlinarith

/-! ### Part 5: 1D state `psi1` and 1D probability lower bound -/

private noncomputable def psi1 (q : ℕ) (γ : ℝ) : EuclideanSpace ℂ (Qubits q) :=
  act (star (gridQFT q))
    (WithLp.toLp 2 fun y : Qubits q =>
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ)) *
        (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ))

private lemma psi1_apply_eq_gridSum (q : ℕ) (γ : ℝ) (k : Qubits q) :
    psi1 q γ k = gridSum q (γ - gridPoint q k) := by
  change (Matrix.mulVec (star (gridQFT q)) _) k = _
  rw [Matrix.mulVec, dotProduct, gridSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [star_gridQFT_apply]
  have hexp :
      Complex.exp (2 * Real.pi * Complex.I *
        ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q k) : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((2 : ℝ) ^ q * (γ - gridPoint q k) * gridPoint q y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (Complex.exp (2 * Real.pi * Complex.I *
        ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q k) : ℝ) : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)) *
      (Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ)) *
        (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ))
      = (Complex.exp (2 * Real.pi * Complex.I *
          ((-((2 : ℝ) ^ q * gridPoint q y * gridPoint q k) : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ))) *
        (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ) * ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)) := by
        push_cast; ring
    _ = Complex.exp (2 * Real.pi * Complex.I *
          (((2 : ℝ) ^ q * (γ - gridPoint q k) * gridPoint q y : ℝ) : ℂ)) *
        (((2 : ℝ) ^ q)⁻¹ : ℂ) := by rw [hexp, sqrt_two_pow_inv_mul_self]

private lemma sum_norm_psi1_sq (q : ℕ) (γ : ℝ) :
    (∑ k : Qubits q, ‖psi1 q γ k‖ ^ 2) = 1 := by
  rw [← EuclideanSpace.norm_sq_eq]
  dsimp [psi1]
  rw [act_norm_of_mem_unitaryGroup (star_gridQFT_mem_unitaryGroup q)]
  rw [EuclideanSpace.norm_sq_eq]
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hterm : ∀ y : Qubits q,
      ‖(WithLp.toLp 2 fun y : Qubits q =>
        Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ)) *
          (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ)) y‖ ^ 2 = ((2 : ℝ) ^ q)⁻¹ := by
    intro y
    change ‖Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ)) *
      (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ)‖ ^ 2 = ((2 : ℝ) ^ q)⁻¹
    rw [norm_mul, mul_pow]
    have h1 : (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (γ * gridPoint q y : ℂ)) =
        2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * (γ * gridPoint q y) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, norm_exp_two_pi_I_mul, one_pow, one_mul]
    rw [Complex.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow, Real.sq_sqrt h2q_pos.le]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ h2q_pos.ne'

private lemma abs_sin_le_pi_mul_norm_psi1 (q : ℕ) (γ : ℝ) (k : Qubits q) :
    |Real.sin (Real.pi * ((2 : ℝ) ^ q * |gridPoint q k - γ|))| ≤
      (Real.pi * ((2 : ℝ) ^ q * |gridPoint q k - γ|)) * ‖psi1 q γ k‖ := by
  let δ : ℝ := γ - gridPoint q k
  have hδ : |gridPoint q k - γ| = |δ| := abs_sub_comm _ _
  rw [hδ, psi1_apply_eq_gridSum]
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have h1 : |Real.sin (Real.pi * ((2 : ℝ) ^ q * |δ|))| = |Real.sin (Real.pi * ((2 : ℝ) ^ q * δ))| := by
    rcases le_total 0 δ with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_nonpos h0, show Real.pi * ((2 : ℝ) ^ q * -δ) = -(Real.pi * ((2 : ℝ) ^ q * δ)) by ring,
        Real.sin_neg, abs_neg]
  rw [h1, ← norm_gridSum_mul_sin q δ]
  have hsin : |Real.sin (Real.pi * δ)| ≤ Real.pi * |δ| := by
    have h : |Real.sin (Real.pi * δ)| ≤ |Real.pi * δ| := Real.abs_sin_le_abs
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h
  have hnonneg : 0 ≤ ‖gridSum q δ‖ * (2 : ℝ) ^ q := mul_nonneg (norm_nonneg _) h2q_pos.le
  nlinarith

private lemma exists_grid_approx (q : ℕ) (hq : 0 < q) (γ : ℝ) (hγ : |γ| ≤ 1 / 3) :
    (∃ k : Qubits q, (2 : ℝ) ^ q * |gridPoint q k - γ| ≤ 1 / 4) ∨
    (∃ k0 k1 : Qubits q, k0 ≠ k1 ∧
      ∃ a : ℝ, 1 / 4 ≤ a ∧ a ≤ 3 / 4 ∧
        (2 : ℝ) ^ q * |gridPoint q k0 - γ| = a ∧
        (2 : ℝ) ^ q * |gridPoint q k1 - γ| = 1 - a) := by
  let u : ℝ := (2 : ℝ) ^ q * (γ + 2⁻¹) - 2⁻¹
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have h2q_ne : (2 : ℝ) ^ q ≠ 0 := h2q_pos.ne'
  have h2q_ge : (2 : ℝ) ≤ (2 : ℝ) ^ q := by
    have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hq
    simpa using h1
  have hgrid : ∀ r : Fin (2 ^ q),
      (2 : ℝ) ^ q * |gridPoint q ((bitsEquivFin q).symm r) - γ| = |u - ((r : ℕ) : ℝ)| := by
    intro r
    rw [abs_sub_comm (gridPoint q ((bitsEquivFin q).symm r)) γ, ← abs_of_pos h2q_pos, ← abs_mul]
    congr 1
    dsimp [u]
    rw [gridPoint_symm, pow_succ]
    calc
      (2 : ℝ) ^ q * (γ - (((r : ℕ) : ℝ) * ((2 : ℝ) ^ q)⁻¹ + (-2⁻¹ + ((2 : ℝ) ^ q * 2)⁻¹)))
        = (2 : ℝ) ^ q * (γ + 2⁻¹) - ((r : ℕ) : ℝ) * ((2 : ℝ) ^ q * ((2 : ℝ) ^ q)⁻¹) -
            ((2 : ℝ) ^ q * ((2 : ℝ) ^ q)⁻¹) * 2⁻¹ := by ring
      _ = (2 : ℝ) ^ q * (γ + 2⁻¹) - 2⁻¹ - ((r : ℕ) : ℝ) := by
          rw [mul_inv_cancel₀ h2q_ne]; ring
  have hγ_bounds := abs_le.mp hγ
  have hu_low : -1 / 4 ≤ u := by
    dsimp [u]; nlinarith
  have hu_high : u ≤ (2 : ℝ) ^ q - 1 + 1 / 4 := by
    dsimp [u]; nlinarith
  by_cases hu1 : u ≤ 1 / 4
  · left
    refine ⟨(bitsEquivFin q).symm ⟨0, Nat.two_pow_pos q⟩, ?_⟩
    rw [hgrid, Nat.cast_zero, sub_zero, abs_le]
    exact ⟨by linarith, hu1⟩
  · have hu1' : 1 / 4 < u := lt_of_not_ge hu1
    by_cases hu2 : (2 : ℝ) ^ q - 1 - 1 / 4 ≤ u
    · left
      have hpos_nat : 0 < 2 ^ q := Nat.two_pow_pos q
      refine ⟨(bitsEquivFin q).symm ⟨2 ^ q - 1, Nat.sub_lt hpos_nat zero_lt_one⟩, ?_⟩
      rw [hgrid]
      have hcast : ((2 ^ q - 1 : ℕ) : ℝ) = (2 : ℝ) ^ q - 1 := by
        rw [Nat.cast_sub hpos_nat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      rw [hcast, abs_le]
      exact ⟨by linarith, by linarith⟩
    · have hu2' : u < (2 : ℝ) ^ q - 1 - 1 / 4 := lt_of_not_ge hu2
      let m : ℕ := ⌊u⌋₊
      have hu_nonneg : 0 ≤ u := by linarith
      have hm_le : (m : ℝ) ≤ u := Nat.floor_le hu_nonneg
      have hu_lt : u < (m : ℝ) + 1 := Nat.lt_floor_add_one u
      have hm1_lt_real : ((m + 1 : ℕ) : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
        push_cast
        linarith
      have hm1_lt : m + 1 < 2 ^ q := Nat.cast_lt.mp hm1_lt_real
      have hm_lt : m < 2 ^ q := by omega
      let r0 : Fin (2 ^ q) := ⟨m, hm_lt⟩
      let r1 : Fin (2 ^ q) := ⟨m + 1, hm1_lt⟩
      let a : ℝ := u - (m : ℝ)
      have ha0 : 0 ≤ a := by dsimp [a]; linarith
      have ha1 : a < 1 := by dsimp [a]; linarith
      have hr0 : (2 : ℝ) ^ q * |gridPoint q ((bitsEquivFin q).symm r0) - γ| = a := by
        rw [hgrid]
        dsimp [r0, a]
        exact abs_of_nonneg ha0
      have hr1 : (2 : ℝ) ^ q * |gridPoint q ((bitsEquivFin q).symm r1) - γ| = 1 - a := by
        rw [hgrid]
        dsimp [r1, a]
        push_cast
        rw [show u - ((m : ℝ) + 1) = -(1 - (u - (m : ℝ))) by ring, abs_neg]
        exact abs_of_nonneg (by linarith)
      by_cases ha_low : a ≤ 1 / 4
      · left
        exact ⟨(bitsEquivFin q).symm r0, by linarith⟩
      · have ha_low' : 1 / 4 < a := lt_of_not_ge ha_low
        by_cases ha_high : 3 / 4 ≤ a
        · left
          exact ⟨(bitsEquivFin q).symm r1, by linarith⟩
        · have ha_high' : a < 3 / 4 := lt_of_not_ge ha_high
          right
          refine ⟨(bitsEquivFin q).symm r0, (bitsEquivFin q).symm r1, ?_, a, ha_low'.le, ha_high'.le, hr0, hr1⟩
          intro heq
          have hfin := (bitsEquivFin q).symm.injective heq
          have hval : m = m + 1 := congrArg Fin.val hfin
          omega

private lemma sum_psi1_sq_gt (q : ℕ) (hq : 0 < q) (γ : ℝ) (hγ : |γ| ≤ 1 / 3) :
    803 / 1000 <
      ∑ k ∈ Finset.univ.filter (fun k : Qubits q => |gridPoint q k - γ| ≤ 1 / (2 : ℝ) ^ q),
        ‖psi1 q γ k‖ ^ 2 := by
  let E1 : Finset (Qubits q) :=
    Finset.univ.filter (fun k : Qubits q => |gridPoint q k - γ| ≤ 1 / (2 : ℝ) ^ q)
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hmem_of_le_one : ∀ k : Qubits q, (2 : ℝ) ^ q * |gridPoint q k - γ| ≤ 1 → k ∈ E1 := by
    intro k hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ k, ?_⟩
    rw [le_div_iff₀ h2q_pos, mul_comm]
    exact hk
  rcases exists_grid_approx q hq γ hγ with ⟨k, hk⟩ | ⟨k0, k1, hk01, a, ha1, ha2, hk0, hk1⟩
  · have hk_mem : k ∈ E1 := hmem_of_le_one k (by linarith)
    let a : ℝ := (2 : ℝ) ^ q * |gridPoint q k - γ|
    have ha0 : 0 ≤ a := mul_nonneg h2q_pos.le (abs_nonneg _)
    have hnorm_ge : 2871 / 3200 ≤ ‖psi1 q γ k‖ := by
      rcases eq_or_lt_of_le ha0 with ha_eq | ha_pos
      · have hdiff0 : γ - gridPoint q k = 0 := by
          have h1 : |gridPoint q k - γ| = 0 := by
            have : (2 : ℝ) ^ q * |gridPoint q k - γ| = 0 := ha_eq.symm
            nlinarith
          have h2 : gridPoint q k - γ = 0 := abs_eq_zero.mp h1
          linarith
        rw [psi1_apply_eq_gridSum, hdiff0, gridSum_zero, norm_one]
        norm_num
      · have hsin_ge := sin_pi_ge_of_quarter ha0 hk
        have hsin_le := abs_sin_le_pi_mul_norm_psi1 q γ k
        change |Real.sin (Real.pi * a)| ≤ (Real.pi * a) * ‖psi1 q γ k‖ at hsin_le
        have hsin_nonneg : 0 ≤ Real.sin (Real.pi * a) := by
          have : 0 ≤ Real.pi * a * (2871 / 3200) := by positivity
          linarith
        rw [abs_of_nonneg hsin_nonneg] at hsin_le
        have hpi_a_pos : 0 < Real.pi * a := mul_pos Real.pi_pos ha_pos
        nlinarith
    have hsq_gt : 803 / 1000 < ‖psi1 q γ k‖ ^ 2 := by nlinarith
    have hle_sum : ‖psi1 q γ k‖ ^ 2 ≤ ∑ k' ∈ E1, ‖psi1 q γ k'‖ ^ 2 :=
      Finset.single_le_sum (fun k' _ => sq_nonneg ‖psi1 q γ k'‖) hk_mem
    linarith
  · have hk0_mem : k0 ∈ E1 := hmem_of_le_one k0 (by linarith)
    have hk1_mem : k1 ∈ E1 := hmem_of_le_one k1 (by linarith)
    have hsub : ({k0, k1} : Finset (Qubits q)) ⊆ E1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hk0_mem
      · rw [Finset.mem_singleton.mp hx]
        exact hk1_mem
    have hpair_le :
        ‖psi1 q γ k0‖ ^ 2 + ‖psi1 q γ k1‖ ^ 2 ≤ ∑ k ∈ E1, ‖psi1 q γ k‖ ^ 2 := by
      have hpair_eq : (∑ k ∈ ({k0, k1} : Finset (Qubits q)), ‖psi1 q γ k‖ ^ 2) =
          ‖psi1 q γ k0‖ ^ 2 + ‖psi1 q γ k1‖ ^ 2 := Finset.sum_pair hk01
      rw [← hpair_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    have ha_pos : 0 < a := by linarith
    have h1a_pos : 0 < 1 - a := by linarith
    have hpi_a_pos : 0 < Real.pi * a := mul_pos Real.pi_pos ha_pos
    have hpi_1a_pos : 0 < Real.pi * (1 - a) := mul_pos Real.pi_pos h1a_pos
    have h0_bound : Real.sin (Real.pi * a) ^ 2 / (Real.pi * a) ^ 2 ≤ ‖psi1 q γ k0‖ ^ 2 := by
      have hle := abs_sin_le_pi_mul_norm_psi1 q γ k0
      rw [hk0] at hle
      have hsq : |Real.sin (Real.pi * a)| ^ 2 ≤ ((Real.pi * a) * ‖psi1 q γ k0‖) ^ 2 := by
        nlinarith [abs_nonneg (Real.sin (Real.pi * a))]
      rw [sq_abs, mul_pow] at hsq
      rw [div_le_iff₀ (sq_pos_of_pos hpi_a_pos)]
      linarith
    have h1_bound :
        Real.sin (Real.pi * (1 - a)) ^ 2 / (Real.pi * (1 - a)) ^ 2 ≤ ‖psi1 q γ k1‖ ^ 2 := by
      have hle := abs_sin_le_pi_mul_norm_psi1 q γ k1
      rw [hk1] at hle
      have hsq : |Real.sin (Real.pi * (1 - a))| ^ 2 ≤ ((Real.pi * (1 - a)) * ‖psi1 q γ k1‖) ^ 2 := by
        nlinarith [abs_nonneg (Real.sin (Real.pi * (1 - a)))]
      rw [sq_abs, mul_pow] at hsq
      rw [div_le_iff₀ (sq_pos_of_pos hpi_1a_pos)]
      linarith
    have htwo := two_point_sin_bound ha1 ha2
    linarith

/-! ### Part 6: Factorization of linear `gradientAlgState` and final probability bound -/

private lemma gradientAlgState_linear_apply (d q : ℕ) (b : ℝ) (g : Fin d → ℝ)
    (k : Fin d → Qubits q) :
    gradientAlgState d q (fun z => ∑ i, g i * z i + b) k =
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (b : ℂ)) *
        ∏ i : Fin d, psi1 q (g i) (k i) := by
  let l : (Fin d → ℝ) → ℝ := fun z => ∑ i, g i * z i + b
  have hprod :
      (∏ i : Fin d, psi1 q (g i) (k i)) =
        ∑ x : Fin d → Qubits q,
          ∏ i : Fin d,
            ((star (gridQFT q)) (k i) (x i) *
              (Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (g i * gridPoint q (x i) : ℂ)) *
                (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ))) := by
    exact Fintype.prod_sum fun i y =>
      (star (gridQFT q)) (k i) y *
        (Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (g i * gridPoint q y : ℂ)) *
          (((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℝ) : ℂ))
  rw [hprod, Finset.mul_sum]
  change (Matrix.mulVec (piKron d (star (gridQFT q))) (WithLp.ofLp (phaseState d q l))) k = _
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [phaseState_apply]
  simp only [piKron, Matrix.of_apply, l]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hexp :
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * ((∑ i, g i * gridPoint q (x i) + b : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (b : ℂ)) *
        Complex.exp (∑ i : Fin d, 2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (g i * gridPoint q (x i) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rw [mul_add, Finset.mul_sum, add_comm]
  rw [hexp]
  ring

private lemma prob_eq_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (z : ι) :
    prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

private lemma probEvent_linear_gt (d q : ℕ) (hq : 0 < q) (b : ℝ) (g : Fin d → ℝ)
    (hg : ∀ i, |g i| ≤ 1 / 3) (j : Fin d) :
    (896 / 1000) ^ 2 <
      probEvent (gradientAlgState d q (fun z => ∑ i, g i * z i + b))
        fun k => |gridPoint q (k j) - g j| ≤ 1 / (2 : ℝ) ^ q := by
  let l : (Fin d → ℝ) → ℝ := fun z => ∑ i, g i * z i + b
  let P : Qubits q → Prop := fun x => |gridPoint q x - g j| ≤ 1 / (2 : ℝ) ^ q
  let w : Fin d → Qubits q → ℝ := fun i x => ‖psi1 q (g i) x‖ ^ 2
  let w' : Fin d → Qubits q → ℝ := fun i x => if i = j then (if P x then w i x else 0) else w i x
  have hprob : ∀ k : Fin d → Qubits q, prob (gradientAlgState d q l) k = ∏ i : Fin d, w i (k i) := by
    intro k
    rw [prob_eq_norm_sq, gradientAlgState_linear_apply, norm_mul, mul_pow]
    have h1 : (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (b : ℂ)) =
        2 * Real.pi * Complex.I * (((2 : ℝ) ^ q * b : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, norm_exp_two_pi_I_mul, one_pow, one_mul, norm_prod, ← Finset.prod_pow]
  have hprod_w' : ∀ k : Fin d → Qubits q,
      (if P (k j) then ∏ i : Fin d, w i (k i) else 0) = ∏ i : Fin d, w' i (k i) := by
    intro k
    by_cases hPk : P (k j)
    · rw [if_pos hPk]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hij : i = j
      · subst hij; dsimp [w']; rw [if_pos rfl, if_pos hPk]
      · dsimp [w']; rw [if_neg hij]
    · rw [if_neg hPk]
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      dsimp [w']
      rw [if_pos rfl, if_neg hPk]
  have hevent :
      probEvent (gradientAlgState d q l) (fun k => P (k j)) =
        ∑ x ∈ Finset.univ.filter P, w j x := by
    rw [probEvent]
    simp_rw [hprob]
    rw [Finset.sum_filter]
    simp_rw [hprod_w']
    rw [← Fintype.prod_sum]
    have hfactor : ∀ i : Fin d,
        (∑ x : Qubits q, w' i x) = if i = j then ∑ x ∈ Finset.univ.filter P, w j x else 1 := by
      intro i
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        dsimp [w']
        rw [if_pos rfl]
      · rw [if_neg hij]
        have : (∑ x : Qubits q, w' i x) = ∑ x : Qubits q, w i x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          dsimp [w']
          rw [if_neg hij]
        rw [this]
        exact sum_norm_psi1_sq q (g i)
    simp_rw [hfactor]
    simp [Finset.prod_ite_eq']
  change (896 / 1000) ^ 2 < probEvent (gradientAlgState d q l) (fun k => P (k j))
  rw [hevent]
  have h1d := sum_psi1_sq_gt q hq (g j) (hg j)
  have hnum : (896 / 1000 : ℝ) ^ 2 < 803 / 1000 := by norm_num
  linarith

private noncomputable def projEvent {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun k => if P k then v k else 0

private lemma norm_projEvent_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] (v : EuclideanSpace ℂ ι) :
    ‖projEvent P v‖ ^ 2 = probEvent v P := by
  rw [EuclideanSpace.norm_sq_eq, probEvent]
  simp_rw [prob_eq_norm_sq]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  change ‖(if P k then v k else 0)‖ ^ 2 = if P k then ‖v k‖ ^ 2 else 0
  split_ifs <;> simp

private lemma norm_projEvent_sub_le {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (ψ φ : EuclideanSpace ℂ ι) :
    ‖projEvent P ψ - projEvent P φ‖ ≤ ‖ψ - φ‖ := by
  have hsq : ‖projEvent P ψ - projEvent P φ‖ ^ 2 ≤ ‖ψ - φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun k _ => ?_
    change ‖(if P k then ψ k else 0) - (if P k then φ k else 0)‖ ^ 2 ≤ ‖ψ k - φ k‖ ^ 2
    split_ifs
    · exact le_rfl
    · simp
  have h1 : 0 ≤ ‖projEvent P ψ - projEvent P φ‖ := norm_nonneg _
  have h2 : 0 ≤ ‖ψ - φ‖ := norm_nonneg _
  nlinarith

theorem solution (d q : ℕ) (hq : 0 < q) (b : ℝ) (g : Fin d → ℝ)
    (hg : ∀ i, |g i| ≤ 1 / 3) (f : (Fin d → ℝ) → ℝ)
    (hf : (999 / 1000 : ℝ) * (2 : ℝ) ^ (d * q) ≤
      ((Finset.univ.filter fun x : Fin d → Qubits q =>
          |f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b| ≤
            1 / (20 * Real.pi * (2 : ℝ) ^ q)).card : ℝ)) :
    ∀ j : Fin d, 3 / 5 < probEvent (gradientAlgState d q f)
      fun k => |gridPoint q (k j) - g j| ≤ 1 / (2 : ℝ) ^ q := by
  intro j
  let l : (Fin d → ℝ) → ℝ := fun z => ∑ i, g i * z i + b
  let ψ : EuclideanSpace ℂ (Fin d → Qubits q) := gradientAlgState d q f
  let φ : EuclideanSpace ℂ (Fin d → Qubits q) := gradientAlgState d q l
  let E : (Fin d → Qubits q) → Prop := fun k => |gridPoint q (k j) - g j| ≤ 1 / (2 : ℝ) ^ q
  have hφ_sq : (896 / 1000) ^ 2 < ‖projEvent E φ‖ ^ 2 := by
    rw [norm_projEvent_sq]
    exact probEvent_linear_gt d q hq b g hg j
  have hφ_norm : 896 / 1000 < ‖projEvent E φ‖ := by
    have h0 : 0 ≤ ‖projEvent E φ‖ := norm_nonneg _
    nlinarith
  have hdiff : ‖ψ - φ‖ ≤ 119 / 1000 := norm_gradientAlgState_sub_le d q b g f hf
  have hproj_diff : ‖projEvent E φ - projEvent E ψ‖ ≤ 119 / 1000 := by
    rw [norm_sub_rev]
    exact (norm_projEvent_sub_le E ψ φ).trans hdiff
  have htri : ‖projEvent E φ‖ - ‖projEvent E ψ‖ ≤ ‖projEvent E φ - projEvent E ψ‖ :=
    norm_sub_norm_le (projEvent E φ) (projEvent E ψ)
  have hψ_norm : 777 / 1000 < ‖projEvent E ψ‖ := by linarith
  have hψ_sq : (777 / 1000) ^ 2 < ‖projEvent E ψ‖ ^ 2 := by nlinarith
  rw [← norm_projEvent_sq]
  have hnum : (3 / 5 : ℝ) < (777 / 1000) ^ 2 := by norm_num
  linarith

end
