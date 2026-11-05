-- Prove2me | solution 1 for SpikedWishart.SoftEdge.J_far_all
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:48:44.93453+00:00
-- url     : https://prove2.me/submissions/68c4fce3-ae70-4370-94d4-019141cbc1a5

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false

open Complex

namespace P31J5
open SpikedWishart.SoftEdge MeasureTheory


/-- The `𝓙` integrand (BBP (104)) as a function of `z`. -/
noncomputable def hJ {r : ℕ} (γ q v : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) *
    (((pc γ : ℂ) - z) ^ k * gFn k π z)

/-- Pointwise rescaling, `𝓙` side: with `a = σ(z - p_c)`, `q = p_c - ε/σ`,
`Z_M⁻¹ · (𝓙-integrand at z) = e^{εv} · e^{va} e^{-M(f(z)-f(p_c))} (g(z)/g(p_c)) a^k`. -/
theorem rescale_ptJ {r : ℕ} (γ q ε v σ : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) (hσ : 0 < σ)
    (hσdef : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) (hq : q = pc γ - ε / σ)
    (hg : gFn k π (pc γ) ≠ 0) :
    (ZM γ q M k π)⁻¹ * hJ γ q v M k π z =
      ((Real.exp (ε * v) : ℝ) : ℂ) *
        (exp ((v : ℂ) * ((σ : ℂ) * (z - pc γ))) *
          (exp (-(M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) * (gFn k π z / gFn k π (pc γ))) *
          ((σ : ℂ) * (z - pc γ)) ^ k) := by
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have e1 : exp (((σ * v : ℝ) : ℂ) * (z - q)) =
      ((Real.exp (ε * v) : ℝ) : ℂ) * exp ((v : ℂ) * ((σ : ℂ) * (z - pc γ))) := by
    rw [ofReal_exp, ← Complex.exp_add]; congr 1; rw [hq]; push_cast; field_simp; ring
  have e2 : exp (-(M : ℂ) * fFn γ q z) =
      exp (-(M : ℂ) * fFn γ q (pc γ)) * exp (-(M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : ((σ : ℂ) * (z - pc γ)) ^ k = (-(σ : ℂ)) ^ k * ((pc γ : ℂ) - z) ^ k := by
    rw [← mul_pow]; ring
  have e4 : exp (-(M : ℂ) * fFn γ q (pc γ)) = (exp ((M : ℂ) * fFn γ q (pc γ)))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  unfold ZM hJ
  rw [hσdef, e1, e2, e3, e4]
  have hE : exp ((M : ℂ) * fFn γ q (pc γ)) ≠ 0 := Complex.exp_ne_zero _
  have hs : (-(σ : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hσ0)
  field_simp

theorem re_fFn (γ q : ℝ) (z : ℂ) : (fFn γ q z).re =
    -(mu γ) * (z.re - q) + Real.log ‖z‖ - (1 / γ ^ 2) * Real.log ‖1 - z‖ := by
  unfold fFn
  have e : (1 / (γ : ℂ) ^ 2) = ((1 / γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, sub_re, add_re, neg_mul, neg_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    log_re, log_re, sub_re, ofReal_re]
  ring

theorem re_fFn_conj (γ q : ℝ) (z : ℂ) :
    (fFn γ q ((starRingEnd ℂ) z)).re = (fFn γ q z).re := by
  rw [re_fFn, re_fFn]
  have h1 : (1 : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) (1 - z) := by simp
  rw [h1, Complex.norm_conj, Complex.norm_conj, conj_re]


theorem cubic_lin (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ) (m : ℝ) (hm : 1 ≤ m) :
    A * m - κ * m ^ 3 ≤ A * max 1 (A / κ) := by
  rcases le_or_gt m (max 1 (A / κ)) with h | h
  · have h1 : A * m ≤ A * max 1 (A / κ) := mul_le_mul_of_nonneg_left h hA
    have h2 : 0 ≤ κ * m ^ 3 := by positivity
    linarith only [h1, h2]
  · have h1 : A / κ < m := lt_of_le_of_lt (le_max_right _ _) h
    have h2 : A < κ * m := by rw [div_lt_iff₀ hκ] at h1; linarith only [h1]
    have h3 : 0 ≤ A * max 1 (A / κ) := mul_nonneg hA (le_trans zero_le_one (le_max_left _ _))
    have h4 : A * m ≤ κ * m * m := mul_le_mul_of_nonneg_right h2.le (by linarith only [hm])
    have h5 : 0 ≤ κ * m * m * (m - 1) := mul_nonneg (by positivity) (by linarith only [hm])
    nlinarith

theorem far_m_bound (P κ Nmax : ℝ) (hκ : 0 < κ) (hP : 0 ≤ P) (hN : 0 ≤ Nmax) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m ν : ℝ, 1 ≤ m → 0 ≤ ν → ν ≤ Nmax →
      ν * m * Real.exp (P * (ν * m)) * Real.exp (-(m ^ 3) * κ) ≤ D / m := by
  have hA : 0 ≤ 2 + P * Nmax := by positivity
  refine ⟨Nmax * Real.exp ((2 + P * Nmax) * max 1 ((2 + P * Nmax) / κ)), by positivity, ?_⟩
  intro m ν hm hν hνN
  have hm0 : 0 < m := by linarith only [hm]
  rw [le_div_iff₀ hm0]
  have hme : m ≤ Real.exp m := by have := Real.add_one_le_exp m; linarith only [this]
  have hm2 : m * m ≤ Real.exp (2 * m) := by
    rw [show 2 * m = m + m by ring, Real.exp_add]
    exact mul_le_mul hme hme hm0.le (Real.exp_pos _).le
  have hPν : P * (ν * m) ≤ P * Nmax * m := by
    have := mul_le_mul_of_nonneg_right hνN hm0.le
    have := mul_le_mul_of_nonneg_left this hP
    linarith only [this]
  have hc := cubic_lin (2 + P * Nmax) κ hA hκ m hm
  have e1 : Real.exp (P * (ν * m) + -(m ^ 3) * κ) ≤ Real.exp (P * Nmax * m + -(m ^ 3) * κ) :=
    Real.exp_le_exp.2 (by linarith only [hPν])
  calc ν * m * Real.exp (P * (ν * m)) * Real.exp (-(m ^ 3) * κ) * m
      = ν * (m * m) * Real.exp (P * (ν * m) + -(m ^ 3) * κ) := by rw [Real.exp_add]; ring
    _ ≤ Nmax * Real.exp (2 * m) * Real.exp (P * Nmax * m + -(m ^ 3) * κ) :=
        mul_le_mul (mul_le_mul hνN hm2 (by positivity) hN) e1 (Real.exp_pos _).le
          (by positivity)
    _ = Nmax * Real.exp ((2 + P * Nmax) * m - κ * m ^ 3) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Nmax * Real.exp ((2 + P * Nmax) * max 1 ((2 + P * Nmax) / κ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hc) hN

theorem sqrt3_bounds : 1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h0 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

theorem omega2_re_im : (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)).re = -(1 / 2) ∧
    (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)).im = Real.sqrt 3 / 2 ∧
    (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)).re = -(1 / 2) ∧
    (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)).im = -(Real.sqrt 3 / 2) := by
  have e : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have e' : -2 * Real.pi / 3 = -(Real.pi - Real.pi / 3) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exp_ofReal_mul_I_re, e, Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, e, Real.sin_pi_sub, Real.sin_pi_div_three]
  · rw [exp_ofReal_mul_I_re, e', Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, e', Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_three]


theorem omega2_conj : exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) =
    (starRingEnd ℂ) (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

/-- `‖g(z)/g(p_c)‖` is bounded on the far part of `Σ*` (`z` at least `δ/2` from `1`, within `L`
of `p_c`, and the `π_j` (`j ≥ k`) at least `d` from `p_c`). -/
theorem gratioJ {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (γ P₀ L d δ : ℝ) (z : ℂ) (hpc0 : 0 < pc γ)
    (hpc1 : pc γ < 1) (hd : 0 < d) (hδ : 0 < δ) (hdA : d ≤ P₀ + 2 + L) (hL : 0 ≤ L)
    (hπ : ∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀)
    (hπd : ∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖)
    (hzL : ‖z - pc γ‖ ≤ L) (h1 : δ / 2 ≤ ‖1 - z‖) :
    gFn k π (pc γ) ≠ 0 ∧
      ‖gFn k π z / gFn k π (pc γ)‖ ≤ ((P₀ + 2 + L) / d) ^ r * (2 / δ) ^ r := by
  set S := Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)) with hS
  set A := P₀ + 2 + L with hA
  have h1pc0 : (1 : ℂ) - pc γ ≠ 0 := by
    rw [show (1 : ℂ) - (pc γ : ℂ) = ((1 - pc γ : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by linarith only [hpc1] : (1 : ℝ) - pc γ ≠ 0)
  have hpne : ∏ j ∈ S, ((π j : ℂ) - pc γ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j hj
    have := hπd j (Finset.mem_filter.1 hj).2
    intro h; rw [h, norm_zero] at this; linarith only [hd, this]
  have hg : gFn k π (pc γ) ≠ 0 := by
    unfold gFn; exact mul_ne_zero (one_div_ne_zero (pow_ne_zero _ h1pc0)) hpne
  refine ⟨hg, ?_⟩
  have hnz : ‖gFn k π z‖ = (∏ j ∈ S, ‖(π j : ℂ) - z‖) / ‖1 - z‖ ^ r := by
    unfold gFn; rw [norm_mul, norm_div, norm_one, norm_pow, norm_prod]; ring
  have hnp : ‖gFn k π (pc γ)‖ = (∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖) / ‖1 - (pc γ : ℂ)‖ ^ r := by
    unfold gFn; rw [norm_mul, norm_div, norm_one, norm_pow, norm_prod]; ring
  have h1pc : ‖1 - (pc γ : ℂ)‖ = 1 - pc γ := by
    rw [show (1 : ℂ) - (pc γ : ℂ) = ((1 - pc γ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith only [hpc1])]
  have hPz : ∏ j ∈ S, ‖(π j : ℂ) - z‖ ≤ A ^ S.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j hj => ?_)
    obtain ⟨h0, hP⟩ := hπ j (Finset.mem_filter.1 hj).2
    have e1 : ‖(π j : ℂ) - pc γ‖ ≤ P₀ + 1 := by
      rw [show (π j : ℂ) - (pc γ : ℂ) = ((π j - pc γ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith only [hpc1, h0, hP, hpc0]
    calc ‖(π j : ℂ) - z‖ = ‖((π j : ℂ) - pc γ) - (z - pc γ)‖ := by ring_nf
      _ ≤ ‖(π j : ℂ) - pc γ‖ + ‖z - pc γ‖ := norm_sub_le _ _
      _ ≤ A := by rw [hA]; linarith only [hzL, e1]
  have hPp : d ^ S.card ≤ ∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖ := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hd.le) (fun j hj => hπd j (Finset.mem_filter.1 hj).2)
  have hc : S.card ≤ r := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun j : Fin r => k ≤ (j : ℕ))
    simpa using this
  have hdpos : 0 < d ^ S.card := pow_pos hd _
  have hPppos : 0 < ∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖ := lt_of_lt_of_le hdpos hPp
  have hz1 : 0 < ‖1 - z‖ := by linarith only [hδ, h1]
  have hbase : 1 ≤ A / d := by rw [le_div_iff₀ hd]; linarith only [hdA]
  have hA0 : 0 ≤ A := by linarith only [hd, hdA]
  have hq1 : (1 - pc γ) ^ r ≤ 1 := pow_le_one₀ (by linarith only [hpc1]) (by linarith only [hpc0])
  have hq2 : (δ / 2) ^ r ≤ ‖1 - z‖ ^ r := pow_le_pow_left₀ (by positivity) h1 r
  rw [norm_div, hnz, hnp, h1pc]
  calc (∏ j ∈ S, ‖(π j : ℂ) - z‖) / ‖1 - z‖ ^ r /
        ((∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖) / (1 - pc γ) ^ r)
      = ((∏ j ∈ S, ‖(π j : ℂ) - z‖) / ∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖) *
          ((1 - pc γ) ^ r / ‖1 - z‖ ^ r) := by
        have : (1 - pc γ) ^ r ≠ 0 := pow_ne_zero _ (by linarith only [hpc1])
        field_simp
    _ ≤ (A ^ S.card / d ^ S.card) * (1 / (δ / 2) ^ r) :=
        mul_le_mul (div_le_div₀ (pow_nonneg hA0 _) hPz hdpos hPp)
          (div_le_div₀ zero_le_one hq1 (by positivity) hq2) (by positivity) (by positivity)
    _ = (A / d) ^ S.card * (2 / δ) ^ r := by
        rw [div_pow A d, div_pow (2 : ℝ) δ, div_pow δ 2, one_div, inv_div]
    _ ≤ (A / d) ^ r * (2 / δ) ^ r :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hc) (by positivity)

/-- Pointwise far bound, `𝓙` side. -/
theorem far_ptJ {r : ℕ} (π : Fin r → ℝ) (γ q ε v V₀ σ δ L κ G : ℝ) (M k : ℕ) (z : ℂ)
    (hσ : 0 < σ) (hσdef : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) (hq : q = pc γ - ε / σ)
    (hg0 : gFn k π (pc γ) ≠ 0) (hv : V₀ ≤ v) (hL : 0 ≤ L) (hε : 0 < ε) (hδ : 0 < δ)
    (h4 : 4 * ε ≤ σ * δ)
    (hre : (z - pc γ).re ≤ -(δ / 2)) (hzL : ‖z - pc γ‖ ≤ L)
    (hf : (-fFn γ q z).re - (-fFn γ q (pc γ)).re ≤ -κ)
    (hG : ‖gFn k π z / gFn k π (pc γ)‖ ≤ G) :
    ‖(ZM γ q M k π)⁻¹ * hJ γ q v M k π z‖ ≤
      Real.exp (-ε * v) * (Real.exp ((max 0 (-V₀) + k) * σ * L) * Real.exp (-(M : ℝ) * κ) * G) := by
  rw [rescale_ptJ γ q ε v σ M k π z hσ hσdef hq hg0]
  simp only [norm_mul, norm_pow]
  rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg hσ.le, Complex.norm_exp, Complex.norm_exp]
  have e1 : ((v : ℂ) * ((σ : ℂ) * (z - pc γ))).re = v * σ * (z - pc γ).re := by
    simp [Complex.mul_re]; ring
  have e2 : (-(M : ℂ) * (fFn γ q z - fFn γ q (pc γ))).re =
      (M : ℝ) * ((-fFn γ q z).re - (-fFn γ q (pc γ)).re) := by
    simp [Complex.mul_re]; ring
  rw [e1, e2]
  set P := max 0 (-V₀) with hP
  have hP0 : 0 ≤ P := le_max_left _ _
  have hvP : -v ≤ P := le_trans (neg_le_neg hv) (le_max_right _ _)
  have hx1 : ε * v + v * σ * (z - pc γ).re ≤ -ε * v + P * σ * L := by
    rcases le_total 0 v with h | h
    · have h1 : v * (σ * (z - pc γ).re) ≤ v * (σ * (-(δ / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hre hσ.le) h
      have h2 : v * (4 * ε) ≤ v * (σ * δ) := mul_le_mul_of_nonneg_left h4 h
      have h3 : 0 ≤ P * σ * L := by positivity
      nlinarith
    · have hρ : 0 ≤ -(z - pc γ).re := by linarith only [hδ, hre]
      have hρL : -(z - pc γ).re ≤ L := by
        have := Complex.abs_re_le_norm (z - pc γ)
        rw [abs_le] at this; linarith only [hzL, this]
      have h1 : (-v) * (σ * -(z - pc γ).re) ≤ P * (σ * L) :=
        mul_le_mul hvP (mul_le_mul_of_nonneg_left hρL hσ.le) (by positivity) hP0
      have h2 : ε * v ≤ -ε * v := by nlinarith
      nlinarith
  have hx2 : (M : ℝ) * ((-fFn γ q z).re - (-fFn γ q (pc γ)).re) ≤ -(M : ℝ) * κ := by
    have := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith only [this]
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  have A1 : Real.exp (ε * v) * Real.exp (v * σ * (z - pc γ).re) ≤
      Real.exp (-ε * v) * Real.exp (P * σ * L) := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.2 hx1
  have A2 : Real.exp ((M : ℝ) * ((-fFn γ q z).re - (-fFn γ q (pc γ)).re)) *
      ‖gFn k π z / gFn k π (pc γ)‖ ≤ Real.exp (-(M : ℝ) * κ) * G :=
    mul_le_mul (Real.exp_le_exp.2 hx2) hG (norm_nonneg _) (Real.exp_pos _).le
  have A3 : (σ * ‖z - pc γ‖) ^ k ≤ Real.exp ((k : ℝ) * σ * L) := by
    rw [mul_assoc, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    have h1 : σ * ‖z - pc γ‖ ≤ σ * L := mul_le_mul_of_nonneg_left hzL hσ.le
    have h2 := Real.add_one_le_exp (σ * L)
    linarith only [h1, h2]
  calc Real.exp (ε * v) * (Real.exp (v * σ * (z - pc γ).re) *
        (Real.exp ((M : ℝ) * ((-fFn γ q z).re - (-fFn γ q (pc γ)).re)) *
          ‖gFn k π z / gFn k π (pc γ)‖) * (σ * ‖z - pc γ‖) ^ k)
      = (Real.exp (ε * v) * Real.exp (v * σ * (z - pc γ).re)) *
          (Real.exp ((M : ℝ) * ((-fFn γ q z).re - (-fFn γ q (pc γ)).re)) *
            ‖gFn k π z / gFn k π (pc γ)‖) * (σ * ‖z - pc γ‖) ^ k := by ring
    _ ≤ (Real.exp (-ε * v) * Real.exp (P * σ * L)) * (Real.exp (-(M : ℝ) * κ) * G) *
          Real.exp ((k : ℝ) * σ * L) := by
        apply mul_le_mul (mul_le_mul A1 A2 (by positivity) (by positivity)) A3 (by positivity)
          (by positivity)
    _ = _ := by
        rw [show (P + (k : ℝ)) * σ * L = P * σ * L + (k : ℝ) * σ * L by ring, Real.exp_add]; ring

set_option maxHeartbeats 1000000 in
/-- Generic far piece of `Σ*`. -/
theorem far_genericJ (ε V₀ δ κ L Nmax P₀ d : ℝ) (r k : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hκ : 0 < κ) (hL : 0 ≤ L) (hN : 0 ≤ Nmax) (hP₀ : 0 ≤ P₀) (hd : 0 < d)
    (hdA : d ≤ P₀ + 2 + L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ) (z : ℝ → ℂ) (w : ℂ) (α β : ℝ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 4 * ε ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) →
      (∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖) → ‖w‖ ≤ 1 → |β - α| ≤ L →
      (∀ s ∈ Set.uIoc α β, (z s - pc γ).re ≤ -(δ / 2) ∧ ‖z s - pc γ‖ ≤ L ∧
        (-fFn γ q (z s)).re - (-fFn γ q (pc γ)).re ≤ -κ) →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) * ∫ s in α..β, hJ γ q v M k π (z s) * w‖ ≤
        B * Real.exp (-ε * v) / m := by
  obtain ⟨D, hD0, hD⟩ := far_m_bound ((max 0 (-V₀) + k) * L) κ Nmax hκ
    (mul_nonneg (by positivity) hL) hN
  have hG0 : 0 ≤ ((P₀ + 2 + L) / d) ^ r * (2 / δ) ^ r := by positivity
  refine ⟨L * (((P₀ + 2 + L) / d) ^ r * (2 / δ) ^ r) * D / (2 * Real.pi), by positivity, ?_⟩
  intro π γ q v m σ M z w α β hv hm1 hm3 hγ1 hν0 hνN hσdef hσ hq h4 hπ hπd hw hab hpt
  have hm0 : 0 < m := by linarith only [hm1]
  have hγ0 : 0 < γ := by linarith only [hγ1]
  have hν1 : 0 < nu γ := by unfold nu; positivity
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hpc0 : 0 < pc γ := by unfold pc; positivity
  have hpc1 : pc γ < 1 := by unfold pc; rw [div_lt_one (by linarith only [hγ0])]; linarith only []
  set G := ((P₀ + 2 + L) / d) ^ r * (2 / δ) ^ r with hGdef
  set X := Real.exp (-ε * v) * (Real.exp ((max 0 (-V₀) + k) * σ * L) *
    Real.exp (-(M : ℝ) * κ) * G) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hX : ∀ s ∈ Set.uIoc α β, ‖(ZM γ q M k π)⁻¹ * (hJ γ q v M k π (z s) * w)‖ ≤ X := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hpt s hs
    have h1z : δ / 2 ≤ ‖1 - z s‖ := by
      have := Complex.abs_re_le_norm (1 - z s)
      have e : (1 - z s).re = (1 - pc γ) - (z s - pc γ).re := by simp
      rw [e, abs_of_nonneg (by linarith only [hδ, hpc1, h1])] at this; linarith only [hpc1, h1, this]
    obtain ⟨hg0, hG⟩ := gratioJ k π γ P₀ L d δ (z s) hpc0 hpc1 hd hδ hdA hL hπ hπd h2 h1z
    have hp := far_ptJ π γ q ε v V₀ σ δ L κ G M k (z s) hσ0 hσdef hq hg0 hv hL hε hδ h4 h1 h2 h3 hG
    calc ‖(ZM γ q M k π)⁻¹ * (hJ γ q v M k π (z s) * w)‖
        = ‖(ZM γ q M k π)⁻¹ * hJ γ q v M k π (z s)‖ * ‖w‖ := by rw [← mul_assoc, norm_mul]
      _ ≤ X * 1 := mul_le_mul hp hw (norm_nonneg _) hX0
      _ = X := mul_one _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hX
  rw [intervalIntegral.integral_const_mul] at hint
  have hc : ‖((σ / (2 * Real.pi) : ℝ) : ℂ)‖ = σ / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hDm := hD m (nu γ) hm1 hν0 hνN
  have e5 : (max 0 (-V₀) + k) * σ * L = (max 0 (-V₀) + k) * L * (nu γ * m) := by rw [hσ]; ring
  have e6 : -(M : ℝ) * κ = -(m ^ 3) * κ := by rw [hm3]
  calc ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) * ∫ s in α..β, hJ γ q v M k π (z s) * w‖
      = σ / (2 * Real.pi) * ‖(ZM γ q M k π)⁻¹ * ∫ s in α..β, hJ γ q v M k π (z s) * w‖ := by
        rw [mul_comm (ZM γ q M k π)⁻¹, mul_assoc, norm_mul, hc]
    _ ≤ σ / (2 * Real.pi) * (X * |β - α|) := by gcongr
    _ ≤ σ / (2 * Real.pi) * (X * L) := by gcongr
    _ = (L * G / (2 * Real.pi)) * Real.exp (-ε * v) *
          (nu γ * m * Real.exp ((max 0 (-V₀) + k) * L * (nu γ * m)) * Real.exp (-(m ^ 3) * κ)) := by
        rw [hXdef, e5, e6, hσ]; ring
    _ ≤ (L * G / (2 * Real.pi)) * Real.exp (-ε * v) * (D / m) := by gcongr
    _ = L * G * D / (2 * Real.pi) * Real.exp (-ε * v) / m := by ring

/-- Cubic decay at the start of the far ray, `𝓙` side: `Re(-f)(p_c + δω₂) ≤ Re(-f)(p_c) - δ³/6`. -/
theorem hdecJ (γ q δ C₁ : ℝ) (hν : 1 ≤ nu γ) (hδ : 0 < δ) (hC : C₁ * δ ≤ 1 / 6)
    (hT : ‖fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) - fFn γ q (pc γ) -
      ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
        pc γ) ^ 3‖ ≤
      C₁ * ‖(pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - pc γ‖ ^ 4) :
    (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
      (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) := by
  set z : ℂ := (pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) with hz
  have hn : ‖z - pc γ‖ = δ := by
    rw [hz, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
      Real.norm_of_nonneg hδ.le]
  have hcube : (z - pc γ) ^ 3 = ((δ ^ 3 : ℝ) : ℂ) := by
    rw [hz, add_sub_cancel_left, mul_pow, ← Complex.exp_nat_mul]
    have : ((3 : ℕ) : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * I) = 2 * (Real.pi : ℂ) * I := by
      push_cast; ring
    rw [this, exp_two_pi_mul_I]; push_cast; ring
  rw [hn, hcube] at hT
  have hre := Complex.re_le_norm
    (-(fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((δ ^ 3 : ℝ) : ℂ)))
  rw [norm_neg] at hre
  have e : (-(fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((δ ^ 3 : ℝ) : ℂ))).re =
      (-fFn γ q z).re - (-fFn γ q (pc γ)).re + nu γ ^ 3 / 3 * δ ^ 3 := by
    rw [← ofReal_mul]; simp only [neg_re, sub_re, ofReal_re]; ring
  rw [e] at hre
  have hν3 : 1 ≤ nu γ ^ 3 := one_le_pow₀ hν
  have hd3 : 0 ≤ δ ^ 3 := by positivity
  have h4 : C₁ * δ ^ 4 ≤ δ ^ 3 / 6 := by
    have : C₁ * δ ^ 4 = (C₁ * δ) * δ ^ 3 := by ring
    rw [this]; nlinarith
  nlinarith

/-- The pointwise conditions of `far_genericJ`. -/
def GoodJ (γ q δ L κ : ℝ) (z : ℂ) : Prop :=
  (z - pc γ).re ≤ -(δ / 2) ∧ ‖z - pc γ‖ ≤ L ∧ (-fFn γ q z).re - (-fFn γ q (pc γ)).re ≤ -κ

theorem goodJ_conj (γ q δ L κ : ℝ) (z : ℂ) (h : GoodJ γ q δ L κ z) :
    GoodJ γ q δ L κ ((starRingEnd ℂ) z) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : ‖(starRingEnd ℂ) z - pc γ‖ = ‖z - pc γ‖ := by
    rw [show (starRingEnd ℂ) z - (pc γ : ℂ) = (starRingEnd ℂ) (z - pc γ) by simp,
      Complex.norm_conj]
  have e2 : ((starRingEnd ℂ) z - pc γ).re = (z - pc γ).re := by simp
  have e3 : (-fFn γ q ((starRingEnd ℂ) z)).re = (-fFn γ q z).re := by
    rw [neg_re, neg_re, re_fFn_conj]
  exact ⟨by rw [e2]; exact h1, by rw [e1]; exact h2, by rw [e3]; exact h3⟩

set_option maxHeartbeats 2000000 in
/-- All five far pieces of `Σ*` (`Σ₁` beyond `δ`, `Σ₂`, `Σ₃` and conjugates), BBP proof of
Prop 3.1 (ii), using the monotonicity of Lemma 3.2. -/
theorem far_allJ (ε V₀ γ₀ P₀ δ R Nmax d : ℝ) (r k : ℕ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀)
    (hP₀ : 0 ≤ P₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / (2 * (γ₀ + 1))) (hR : 0 ≤ R) (hN : 0 ≤ Nmax)
    (hd : 0 < d) (hdP : d ≤ P₀ + 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q v m σ ℓ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 4 * ε ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) →
      (∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖) → ℓ = 2 * pc γ →
      3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) ≤ δ →
      StrictAntiOn (fun t : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ)) →
      StrictAntiOn (fun x : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
          (x : ℂ))).re) (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
        (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
          (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
        (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            hJ γ q v M k π (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) * I‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, hJ γ q v M k π
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, hJ γ q v M k π ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
            exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, hJ γ q v M k π ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
            exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, hJ γ q v M k π
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) := by
  have hγ01 : (0 : ℝ) < γ₀ + 1 := by linarith only [hγ₀]
  have hδq : δ ≤ 1 / 4 := by
    have : 1 / (2 * (γ₀ + 1)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hγ₀]
    linarith only [hδ1, this]
  obtain ⟨B, hB0, hB⟩ := far_genericJ ε V₀ δ (δ ^ 3 / 6) (4 + R) Nmax P₀ d r k hε hδ
    (by positivity) (by linarith only [hR]) hN hP₀ hd (by linarith only [hR, hdP])
  refine ⟨B, hB0, ?_⟩
  intro π γ q v m σ ℓ M hv hm1 hm3 hγ1 hγ hν0 hνN hσdef hσ hq h4 hπ hπd hℓ hδ3 h1 h2 h3 hdec
  have hγ0 : 0 < γ := by linarith only [hγ1]
  have hpc0 : 0 < pc γ := by unfold pc; positivity
  have hpc1 : pc γ < 1 := by unfold pc; rw [div_lt_one (by linarith only [hγ0])]; linarith only []
  have hpch : 1 / 2 ≤ pc γ := by
    unfold pc; rw [le_div_iff₀ (by linarith only [hγ0])]; linarith only [hγ1]
  have hδℓ : δ ≤ 2 * pc γ := by linarith only [hδq, hpch]
  obtain ⟨hωr, hωi, hωbr, hωbi⟩ := omega2_re_im
  obtain ⟨hs1, hs2⟩ := sqrt3_bounds
  set ω := exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) with hω
  have hFδ : ∀ t : ℝ, δ ≤ t → t ≤ 2 * pc γ →
      (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * ω)).re ≤ (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * ω)).re :=
    fun t ht1 ht2 => h1.antitoneOn ⟨hδ3, hδℓ⟩ ⟨hδ3.trans ht1, ht2⟩ ht1
  have hF2 : (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * ω)).re ≤
      (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * ω)).re := by
    have := hFδ (2 * pc γ) hδℓ le_rfl
    push_cast at this; exact this
  subst hℓ
  have common := fun (z : ℝ → ℂ) (w : ℂ) (α β : ℝ) (hw : ‖w‖ ≤ 1) (hab : |β - α| ≤ 4 + R)
      (hpt : ∀ s ∈ Set.uIoc α β, GoodJ γ q δ (4 + R) (δ ^ 3 / 6) (z s)) =>
    hB π γ q v m σ M z w α β hv hm1 hm3 hγ1 hν0 hνN hσdef hσ hq h4 hπ hπd hw hab hpt
  have hWn : ‖ω‖ ≤ 1 := by rw [hω, norm_exp_ofReal_mul_I]
  have hWbn : ‖exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤ 1 := by rw [norm_exp_ofReal_mul_I]
  have hab1 : |2 * pc γ - δ| ≤ 4 + R := by rw [abs_of_nonneg (by linarith only [hδℓ])]; linarith only [hδ, hR, hpc1]
  have hab2 : |R - 0| ≤ 4 + R := by rw [sub_zero, abs_of_nonneg hR]; linarith only []
  -- the ray `Σ₁`
  have gray : ∀ t ∈ Set.uIoc δ (2 * pc γ), GoodJ γ q δ (4 + R) (δ ^ 3 / 6)
      ((pc γ : ℂ) + (t : ℂ) * ω) := by
    intro t ht
    rw [Set.uIoc_of_le hδℓ] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hn : ‖(pc γ : ℂ) + (t : ℂ) * ω - pc γ‖ = t := by
      rw [add_sub_cancel_left, norm_mul, hω, norm_exp_ofReal_mul_I, mul_one, norm_real,
        Real.norm_of_nonneg (by linarith only [hδ, ht1])]
    have hre : ((pc γ : ℂ) + (t : ℂ) * ω - pc γ).re = -(t / 2) := by
      rw [add_sub_cancel_left, re_ofReal_mul, hωr]; ring
    refine ⟨by rw [hre]; linarith only [ht1], by rw [hn]; linarith only [hR, hpc1, ht2], ?_⟩
    have := hFδ t ht1.le ht2
    linarith only [hdec, this]
  -- the horizontal piece `Σ₂`
  have ghor : ∀ x ∈ Set.uIoc (0 : ℝ) R, GoodJ γ q δ (4 + R) (δ ^ 3 / 6)
      ((pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ)) := by
    intro x hx
    rw [Set.uIoc_of_le hR] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hsub : (pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ) - pc γ =
        ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ) := by ring
    have hre : ((pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ) - pc γ).re = -pc γ - x := by
      rw [hsub, sub_re, re_ofReal_mul, hωr, ofReal_re]; ring
    have hn : ‖(pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ) - pc γ‖ ≤ 4 + R := by
      rw [hsub]
      calc ‖((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ)‖ ≤ ‖((2 * pc γ : ℝ) : ℂ) * ω‖ + ‖(x : ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 * pc γ + x := by
            rw [norm_mul, hω, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real,
              Real.norm_of_nonneg (by linarith only [hpch]), Real.norm_of_nonneg hx1.le]
        _ ≤ 4 + R := by linarith only [hpc1, hx2]
    refine ⟨by rw [hre]; linarith only [hδℓ, hx1], hn, ?_⟩
    have e2 := h2.antitoneOn ⟨le_refl 0, hR⟩ ⟨hx1.le, hx2⟩ hx1.le
    simp only [ofReal_zero, sub_zero] at e2
    have hc : ((2 * pc γ : ℝ) : ℂ) = 2 * (pc γ : ℂ) := by push_cast; ring
    rw [hc]
    linarith only [hdec, hF2, e2]
  -- the vertical piece `Σ₃`
  have gver : ∀ y ∈ Set.uIoc (-(2 * pc γ * (Real.sqrt 3 / 2))) (2 * pc γ * (Real.sqrt 3 / 2)),
      GoodJ γ q δ (4 + R) (δ ^ 3 / 6) (((pc γ - 2 * pc γ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) := by
    intro y hy
    have hY : 0 ≤ 2 * pc γ * (Real.sqrt 3 / 2) := by positivity
    rw [Set.uIoc_of_le (by linarith only [hY])] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hY' : 2 * pc γ * (Real.sqrt 3 / 2) = Real.sqrt 3 * pc γ := by ring
    have hyabs : |y| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
    have hpt : ((pc γ - 2 * pc γ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I = -(R : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [hpt]
    have hre : (-(R : ℂ) + (y : ℂ) * I - pc γ).re = -R - pc γ := by simp
    have him : (-(R : ℂ) + (y : ℂ) * I - pc γ).im = y := by simp
    have hn : ‖-(R : ℂ) + (y : ℂ) * I - pc γ‖ ≤ 4 + R := by
      have := Complex.norm_le_abs_re_add_abs_im (-(R : ℂ) + (y : ℂ) * I - pc γ)
      rw [hre, him, abs_of_nonpos (by linarith only [hR, hpc0])] at this; linarith only [hpc1, hyabs, this]
    refine ⟨by rw [hre]; linarith only [hR, hδℓ], hn, ?_⟩
    have hf : (-fFn γ q (-(R : ℂ) + (y : ℂ) * I)).re ≤
        (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * ω)).re := by
      rcases le_or_gt 0 y with hy0 | hy0
      · have := h3 (Real.sqrt 3 * pc γ - y) (by linarith only [hy2]) (by linarith only [hy0])
        have e : -(R : ℂ) + ((Real.sqrt 3 * pc γ - (Real.sqrt 3 * pc γ - y) : ℝ) : ℂ) * I =
            -(R : ℂ) + (y : ℂ) * I := by push_cast; ring
        rw [e] at this; exact this
      · have := h3 (Real.sqrt 3 * pc γ + y) (by linarith only [hy1]) (by linarith only [hy0])
        have e : -(R : ℂ) + (y : ℂ) * I = (starRingEnd ℂ)
            (-(R : ℂ) + ((Real.sqrt 3 * pc γ - (Real.sqrt 3 * pc γ + y) : ℝ) : ℂ) * I) := by
          rw [map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
            Complex.conj_I]; push_cast; ring
        rw [e, neg_re, re_fFn_conj, ← neg_re]; exact this
    linarith only [hdec, hF2, hf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hab3 : |2 * pc γ * (Real.sqrt 3 / 2) - -(2 * pc γ * (Real.sqrt 3 / 2))| ≤ 4 + R := by
      have hY : 0 ≤ 2 * pc γ * (Real.sqrt 3 / 2) := by positivity
      rw [abs_of_nonneg (by linarith only [hY])]; nlinarith
    exact common (fun y => ((pc γ - 2 * pc γ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) I _ _
      (by rw [Complex.norm_I]) hab3 gver
  · have := common (fun x => (pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ)) 1 0 R
      (by rw [norm_one]) hab2 ghor
    simpa only [mul_one] using this
  · exact common (fun t => (pc γ : ℂ) + (t : ℂ) * ω) ω δ (2 * pc γ) hWn hab1 gray
  · refine common (fun t => (pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) δ (2 * pc γ) hWbn hab1 (fun t ht => ?_)
    have e : (pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) =
        (starRingEnd ℂ) ((pc γ : ℂ) + (t : ℂ) * ω) := by
      rw [omega2_conj, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    try simp only
    rw [e]
    exact goodJ_conj _ _ _ _ _ _ (gray t ht)
  · have := common (fun x => (pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) *
        exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)) 1 0 R (by rw [norm_one]) hab2
      (fun x hx => by
        have e : (pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) -
            (x : ℂ) = (starRingEnd ℂ) ((pc γ : ℂ) + ((2 * pc γ : ℝ) : ℂ) * ω - (x : ℂ)) := by
          rw [omega2_conj, map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
            Complex.conj_ofReal]
        try simp only
        rw [e]
        exact goodJ_conj _ _ _ _ _ _ (ghor x hx))
    simpa only [mul_one] using this

end P31J5

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε V₀ γ₀ P₀ δ R Nmax d : ℝ) (r k : ℕ), 0 < ε → 1 ≤ γ₀ → 0 ≤ P₀ →
    0 < δ → δ ≤ 1 / (2 * (γ₀ + 1)) → 0 ≤ R → 0 ≤ Nmax → 0 < d → d ≤ P₀ + 1 →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q v m σ ℓ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 4 * ε ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) →
      (∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖) → ℓ = 2 * pc γ →
      3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) ≤ δ →
      StrictAntiOn (fun t : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ)) →
      StrictAntiOn (fun x : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
          (x : ℂ))).re) (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
        (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
          (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
        (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * ((((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) - q)) * exp (-(M : ℂ) * fFn γ q (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I)) * (((pc γ : ℂ) - (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I)) ^ k * gFn k π (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I))) * I‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp (-(M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))) * (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)))) *
            exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp (-(M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))) * (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)))) *
            exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) := by
  exact P31J5.far_allJ
