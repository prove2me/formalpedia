-- Prove2me | solution 1 for SpikedWishart.SoftEdge.H_far_all
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:14:25.010278+00:00
-- url     : https://prove2.me/submissions/79688d06-077c-4dd6-b271-4db52df6095b

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false

open Complex

namespace P31F
open SpikedWishart.SoftEdge MeasureTheory

/-- Pointwise rescaling (BBP (148)): with `a = σ(z - p_c)` and `q = p_c - ε/σ`,
`Z_M · (𝓗-integrand at z) = e^{-εu} · e^{-ua} e^{M(f(z)-f(p_c))} (g(p_c)/g(z)) a^{-k}`. -/
theorem rescale_pt {r : ℕ} (γ q ε u σ : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) (hσ : 0 < σ)
    (hσdef : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) (hq : q = pc γ - ε / σ)
    (hz : (pc γ : ℂ) - z ≠ 0) (hg : gFn k π z ≠ 0) :
    ZM γ q M k π * (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) *
        exp ((M : ℂ) * fFn γ q z) * (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z))) =
      ((Real.exp (-ε * u) : ℝ) : ℂ) *
        (exp (-(u : ℂ) * ((σ : ℂ) * (z - pc γ))) *
          (exp ((M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) * (gFn k π (pc γ) / gFn k π z)) *
          (1 / ((σ : ℂ) * (z - pc γ)) ^ k)) := by
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have e1 : exp (-((σ * u : ℝ) : ℂ) * (z - q)) =
      ((Real.exp (-ε * u) : ℝ) : ℂ) * exp (-(u : ℂ) * ((σ : ℂ) * (z - pc γ))) := by
    rw [ofReal_exp, ← Complex.exp_add]; congr 1; rw [hq]; push_cast; field_simp; ring
  have e2 : exp ((M : ℂ) * fFn γ q z) =
      exp ((M : ℂ) * fFn γ q (pc γ)) * exp ((M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : ((σ : ℂ) * (z - pc γ)) ^ k = (-(σ : ℂ)) ^ k * ((pc γ : ℂ) - z) ^ k := by
    rw [← mul_pow]; ring
  unfold ZM
  rw [hσdef, e1, e2, e3]
  have hE : exp ((M : ℂ) * fFn γ q (pc γ)) ≠ 0 := Complex.exp_ne_zero _
  have hs : (-(σ : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hσ0)
  have hp : ((pc γ : ℂ) - z) ^ k ≠ 0 := pow_ne_zero _ hz
  field_simp


/-- The `𝓗` integrand (BBP (103)) as a function of `z`. -/
noncomputable def hH {r : ℕ} (γ q u : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
    (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z))

theorem omega_re_im : (exp (((Real.pi / 3 : ℝ) : ℂ) * I)).re = 1 / 2 ∧
    (exp (((Real.pi / 3 : ℝ) : ℂ) * I)).im = Real.sqrt 3 / 2 ∧
    (exp (((-Real.pi / 3 : ℝ) : ℂ) * I)).re = 1 / 2 ∧
    (exp (((-Real.pi / 3 : ℝ) : ℂ) * I)).im = -(Real.sqrt 3 / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, Real.sin_pi_div_three]
  · rw [exp_ofReal_mul_I_re, neg_div, Real.cos_neg, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, neg_div, Real.sin_neg, Real.sin_pi_div_three]

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

/-- `‖g(p_c)/g(z)‖` is bounded once `z` stays `d` away from the poles `1`, `π_j`. -/
theorem gFn_ratio_far {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (γ γ₀ P₀ A d : ℝ) (z : ℂ)
    (hγ : 1 ≤ γ) (hγ₀ : γ ≤ γ₀) (hd : 0 < d) (hdP : d ≤ P₀ + 1) (hA : 0 ≤ A)
    (hπ : ∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀)
    (hdist : ∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - z‖) (h1 : d ≤ ‖1 - z‖)
    (hA1 : ‖1 - z‖ ≤ A) :
    gFn k π z ≠ 0 ∧
      ‖gFn k π (pc γ) / gFn k π z‖ ≤ (A * (γ₀ + 1)) ^ r * ((P₀ + 1) / d) ^ r := by
  have hγ0 : 0 < γ := by linarith only [hγ]
  have hpc0 : 0 < pc γ := by unfold pc; positivity
  have hpc1 : pc γ < 1 := by unfold pc; rw [div_lt_one (by linarith only [hγ0])]; linarith only []
  have h1pcv : 1 - pc γ = 1 / (γ + 1) := by unfold pc; field_simp; ring
  have h1z : (1 : ℂ) - z ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith only [hd, h1]
  have hz1pos : 0 < ‖1 - z‖ := by linarith only [hd, h1]
  have hprod_ne : ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j hj
    have := hdist j (Finset.mem_filter.1 hj).2
    intro h; rw [h, norm_zero] at this; linarith only [hd, this]
  have hgz : gFn k π z ≠ 0 := by
    unfold gFn; exact mul_ne_zero (one_div_ne_zero (pow_ne_zero _ h1z)) hprod_ne
  refine ⟨hgz, ?_⟩
  set S := Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)) with hS
  have hnz : ‖gFn k π z‖ = (∏ j ∈ S, ‖(π j : ℂ) - z‖) / ‖1 - z‖ ^ r := by
    unfold gFn; rw [norm_mul, norm_div, norm_one, norm_pow, norm_prod]; ring
  have hnp : ‖gFn k π (pc γ)‖ = (∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖) / ‖1 - (pc γ : ℂ)‖ ^ r := by
    unfold gFn; rw [norm_mul, norm_div, norm_one, norm_pow, norm_prod]; ring
  have h1pc : ‖1 - (pc γ : ℂ)‖ = 1 - pc γ := by
    rw [show (1 : ℂ) - (pc γ : ℂ) = ((1 - pc γ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith only [hpc1])]
  have hPz : d ^ S.card ≤ ∏ j ∈ S, ‖(π j : ℂ) - z‖ := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hd.le) (fun j hj => hdist j (Finset.mem_filter.1 hj).2)
  have hPp : ∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖ ≤ (P₀ + 1) ^ S.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j hj => ?_)
    obtain ⟨h0, hP⟩ := hπ j (Finset.mem_filter.1 hj).2
    rw [show (π j : ℂ) - (pc γ : ℂ) = ((π j - pc γ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hpc1, h0, hP, hpc0]
  have hc : S.card ≤ r := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun j : Fin r => k ≤ (j : ℕ))
    simpa using this
  have hdpos : 0 < d ^ S.card := pow_pos hd _
  have hPzpos : 0 < ∏ j ∈ S, ‖(π j : ℂ) - z‖ := lt_of_lt_of_le hdpos hPz
  have hbase : 1 ≤ (P₀ + 1) / d := by rw [le_div_iff₀ hd]; linarith only [hdP]
  have hP1 : 0 ≤ P₀ + 1 := by linarith only [hd, hdP]
  have hAg : 0 ≤ A * (γ₀ + 1) := mul_nonneg hA (by linarith only [hγ, hγ₀])
  rw [norm_div, hnp, hnz, h1pc, h1pcv]
  calc (∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖) / (1 / (γ + 1)) ^ r /
        ((∏ j ∈ S, ‖(π j : ℂ) - z‖) / ‖1 - z‖ ^ r)
      = ((∏ j ∈ S, ‖(π j : ℂ) - (pc γ : ℂ)‖) / ∏ j ∈ S, ‖(π j : ℂ) - z‖) *
          (‖1 - z‖ * (γ + 1)) ^ r := by
        rw [mul_pow, one_div, inv_pow]; field_simp
    _ ≤ ((P₀ + 1) ^ S.card / d ^ S.card) * (A * (γ₀ + 1)) ^ r := by
        apply mul_le_mul (div_le_div₀ (pow_nonneg hP1 _) hPp hdpos hPz)
          (pow_le_pow_left₀ (by positivity) (mul_le_mul hA1 (by linarith only [hγ₀]) (by linarith only [hγ0]) hA) r)
          (by positivity) (div_nonneg (pow_nonneg hP1 _) hdpos.le)
    _ = ((P₀ + 1) / d) ^ S.card * (A * (γ₀ + 1)) ^ r := by rw [div_pow]
    _ ≤ ((P₀ + 1) / d) ^ r * (A * (γ₀ + 1)) ^ r := by
        apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hc) (pow_nonneg hAg _)
    _ = (A * (γ₀ + 1)) ^ r * ((P₀ + 1) / d) ^ r := by ring

/-- Pointwise far bound (BBP (148) for the far part of `Γ`). -/
theorem far_pt {r : ℕ} (π : Fin r → ℝ) (γ q ε u U₀ σ δ L κ G : ℝ) (M k : ℕ) (z : ℂ)
    (hσ : 0 < σ) (hσdef : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) (hq : q = pc γ - ε / σ) (hu : U₀ ≤ u)
    (hδ : 0 < δ) (hσδ : 1 ≤ σ * δ) (hz1 : δ ≤ ‖z - pc γ‖) (hre0 : 0 ≤ (z - pc γ).re)
    (hreL : (z - pc γ).re ≤ L)
    (hf : (fFn γ q z).re - (fFn γ q (pc γ)).re ≤ -κ) (hg : gFn k π z ≠ 0)
    (hG : ‖gFn k π (pc γ) / gFn k π z‖ ≤ G) :
    ‖ZM γ q M k π * hH γ q u M k π z‖ ≤
      Real.exp (-ε * u) * (Real.exp (max 0 (-U₀) * σ * L) * Real.exp (-(M : ℝ) * κ) * G) := by
  have hzpc : (pc γ : ℂ) - z ≠ 0 := by
    intro h
    have h0 : z - (pc γ : ℂ) = 0 := by rw [← neg_sub, h, neg_zero]
    rw [h0, norm_zero] at hz1; linarith only [hδ, hz1]
  unfold hH
  rw [rescale_pt γ q ε u σ M k π z hσ hσdef hq hzpc hg]
  simp only [norm_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp,
    Complex.norm_exp]
  have e1 : (-(u : ℂ) * ((σ : ℂ) * (z - pc γ))).re = -(u * σ * (z - pc γ).re) := by
    simp [Complex.mul_re]; ring
  have e2 : ((M : ℂ) * (fFn γ q z - fFn γ q (pc γ))).re =
      (M : ℝ) * ((fFn γ q z).re - (fFn γ q (pc γ)).re) := by
    simp [Complex.mul_re]
  rw [e1, e2]
  have hk : ‖1 / ((σ : ℂ) * (z - pc γ)) ^ k‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le]
    apply div_le_one_of_le₀ _ (by positivity)
    apply one_le_pow₀
    have := mul_le_mul_of_nonneg_left hz1 hσ.le
    linarith only [hσδ, this]
  have hx1 : -(u * σ * (z - pc γ).re) ≤ max 0 (-U₀) * σ * L := by
    have h1 : -u ≤ max 0 (-U₀) := le_trans (neg_le_neg hu) (le_max_right _ _)
    have h2 : 0 ≤ max 0 (-U₀) := le_max_left _ _
    have h3 : 0 ≤ σ * (z - pc γ).re := mul_nonneg hσ.le hre0
    have h4 : -(u * σ * (z - pc γ).re) = (-u) * (σ * (z - pc γ).re) := by ring
    rw [h4]
    calc (-u) * (σ * (z - pc γ).re) ≤ max 0 (-U₀) * (σ * (z - pc γ).re) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ ≤ max 0 (-U₀) * (σ * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hreL hσ.le) h2
      _ = max 0 (-U₀) * σ * L := by ring
  have hx2 : (M : ℝ) * ((fFn γ q z).re - (fFn γ q (pc γ)).re) ≤ -(M : ℝ) * κ := by
    have := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith only [this]
  have e3 := Real.exp_le_exp.2 hx1
  have e4 := Real.exp_le_exp.2 hx2
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc Real.exp (-(u * σ * (z - pc γ).re)) *
        (Real.exp ((M : ℝ) * ((fFn γ q z).re - (fFn γ q (pc γ)).re)) *
          ‖gFn k π (pc γ) / gFn k π z‖) * ‖1 / ((σ : ℂ) * (z - pc γ)) ^ k‖
      ≤ Real.exp (max 0 (-U₀) * σ * L) * (Real.exp (-(M : ℝ) * κ) * G) * 1 := by
        apply mul_le_mul _ hk (norm_nonneg _) (by positivity)
        apply mul_le_mul e3 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul e4 hG (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (max 0 (-U₀) * σ * L) * Real.exp (-(M : ℝ) * κ) * G := by ring

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

set_option maxHeartbeats 1000000 in
/-- Generic far piece of `Γ*`: a path that stays `δ` from `p_c`, to the right of `p_c`,
`δ/2` from the poles, inside radius `L`, with `Re f ≤ Re f(p_c) - κ`, contributes
`O(e^{-εu/2}/m)`. -/
theorem far_generic (ε U₀ δ κ L Nmax γ₀ P₀ : ℝ) (r k : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hκ : 0 < κ) (hL : 0 ≤ L) (hN : 0 ≤ Nmax) (hγ₀ : 1 ≤ γ₀) (hP₀ : 0 ≤ P₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q u m σ : ℝ) (M : ℕ) (z : ℝ → ℂ) (w : ℂ) (α β : ℝ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 1 ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) → ‖w‖ ≤ 1 → |β - α| ≤ L →
      (∀ s ∈ Set.uIoc α β, δ ≤ ‖z s - pc γ‖ ∧ 0 ≤ (z s - pc γ).re ∧ ‖z s - pc γ‖ ≤ L ∧
        δ / 2 ≤ ‖1 - z s‖ ∧ (∀ j : Fin r, k ≤ (j : ℕ) → δ / 2 ≤ ‖(π j : ℂ) - z s‖) ∧
        (fFn γ q (z s)).re - (fFn γ q (pc γ)).re ≤ -κ) →
      ‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) * ∫ s in α..β, hH γ q u M k π (z s) * w‖ ≤
        B * Real.exp (-(ε / 2) * u) / m := by
  obtain ⟨D, hD0, hD⟩ := far_m_bound (max 0 (-U₀) * L) κ Nmax hκ
    (mul_nonneg (le_max_left _ _) hL) hN
  have hG0 : 0 ≤ ((1 + L) * (γ₀ + 1)) ^ r * ((P₀ + 1) / (δ / 2)) ^ r := by positivity
  refine ⟨L * (((1 + L) * (γ₀ + 1)) ^ r * ((P₀ + 1) / (δ / 2)) ^ r) *
    Real.exp (ε / 2 * max 0 (-U₀)) * D / (2 * Real.pi), by positivity, ?_⟩
  intro π γ q u m σ M z w α β hu hm1 hm3 hγ1 hγ hν0 hνN hσdef hσ hq hσδ hπ hw hab hpt
  have hm0 : 0 < m := by linarith only [hm1]
  have hσ0 : 0 < σ := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hδ.le
    linarith only [hσδ, this]
  have hγ0 : 0 < γ := by linarith only [hγ1]
  have hpc0 : 0 < pc γ := by unfold pc; positivity
  have hpc1 : pc γ < 1 := by unfold pc; rw [div_lt_one (by linarith only [hγ0])]; linarith only []
  have hpcn : ‖(1 : ℂ) - pc γ‖ ≤ 1 := by
    rw [show (1 : ℂ) - (pc γ : ℂ) = ((1 - pc γ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith only [hpc1])]
    linarith only [hpc0]
  set G := ((1 + L) * (γ₀ + 1)) ^ r * ((P₀ + 1) / (δ / 2)) ^ r with hGdef
  set X := Real.exp (-ε * u) * (Real.exp (max 0 (-U₀) * σ * L) *
    Real.exp (-(M : ℝ) * κ) * G) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hX : ∀ s ∈ Set.uIoc α β, ‖ZM γ q M k π * (hH γ q u M k π (z s) * w)‖ ≤ X := by
    intro s hs
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpt s hs
    have hA1 : ‖1 - z s‖ ≤ 1 + L := by
      calc ‖1 - z s‖ = ‖(1 - (pc γ : ℂ)) - (z s - pc γ)‖ := by ring_nf
        _ ≤ ‖1 - (pc γ : ℂ)‖ + ‖z s - pc γ‖ := norm_sub_le _ _
        _ ≤ 1 + L := add_le_add hpcn h3
    obtain ⟨hg, hG⟩ := gFn_ratio_far k π γ γ₀ P₀ (1 + L) (δ / 2) (z s) hγ1 hγ (by linarith only [hδ])
      (by linarith only [hδ1, hP₀]) (by linarith only [hL]) hπ h5 h4 hA1
    have hre : (z s - pc γ).re ≤ L := le_trans (Complex.re_le_norm _) h3
    have hp := far_pt π γ q ε u U₀ σ δ L κ G M k (z s) hσ0 hσdef hq hu hδ hσδ h1 h2 hre h6 hg hG
    calc ‖ZM γ q M k π * (hH γ q u M k π (z s) * w)‖
        = ‖ZM γ q M k π * hH γ q u M k π (z s)‖ * ‖w‖ := by rw [← mul_assoc, norm_mul]
      _ ≤ X * 1 := mul_le_mul hp hw (norm_nonneg _) hX0
      _ = X := mul_one _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hX
  rw [intervalIntegral.integral_const_mul] at hint
  have hc : ‖((σ / (2 * Real.pi) : ℝ) : ℂ)‖ = σ / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hDm := hD m (nu γ) hm1 hν0 hνN
  have hexp : Real.exp (-ε * u) ≤ Real.exp (-(ε / 2) * u) * Real.exp (ε / 2 * max 0 (-U₀)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : -u ≤ max 0 (-U₀) := le_trans (neg_le_neg hu) (le_max_right _ _)
    nlinarith
  have e5 : max 0 (-U₀) * σ * L = max 0 (-U₀) * L * (nu γ * m) := by rw [hσ]; ring
  have e6 : -(M : ℝ) * κ = -(m ^ 3) * κ := by rw [hm3]
  calc ‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) * ∫ s in α..β, hH γ q u M k π (z s) * w‖
      = σ / (2 * Real.pi) * ‖ZM γ q M k π * ∫ s in α..β, hH γ q u M k π (z s) * w‖ := by
        rw [mul_comm (ZM γ q M k π), mul_assoc, norm_mul, hc]
    _ ≤ σ / (2 * Real.pi) * (X * |β - α|) := by gcongr
    _ ≤ σ / (2 * Real.pi) * (X * L) := by gcongr
    _ = (L * G / (2 * Real.pi)) * Real.exp (-ε * u) *
          (nu γ * m * Real.exp (max 0 (-U₀) * L * (nu γ * m)) * Real.exp (-(m ^ 3) * κ)) := by
        rw [hXdef, e5, e6, hσ]; ring
    _ ≤ (L * G / (2 * Real.pi)) * (Real.exp (-(ε / 2) * u) * Real.exp (ε / 2 * max 0 (-U₀))) *
          (D / m) := by gcongr
    _ = L * G * Real.exp (ε / 2 * max 0 (-U₀)) * D / (2 * Real.pi) *
          Real.exp (-(ε / 2) * u) / m := by ring

/-! ## Far pieces of `Γ*` -/

/-- The pointwise conditions of `far_generic`. -/
def Good {r : ℕ} (γ q δ L κ : ℝ) (k : ℕ) (π : Fin r → ℝ) (z : ℂ) : Prop :=
  δ ≤ ‖z - pc γ‖ ∧ 0 ≤ (z - pc γ).re ∧ ‖z - pc γ‖ ≤ L ∧ δ / 2 ≤ ‖1 - z‖ ∧
    (∀ j : Fin r, k ≤ (j : ℕ) → δ / 2 ≤ ‖(π j : ℂ) - z‖) ∧
    (fFn γ q z).re - (fFn γ q (pc γ)).re ≤ -κ

theorem good_conj {r : ℕ} (γ q δ L κ : ℝ) (k : ℕ) (π : Fin r → ℝ) (z : ℂ)
    (h : Good γ q δ L κ k π z) : Good γ q δ L κ k π ((starRingEnd ℂ) z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have e1 : ‖(starRingEnd ℂ) z - pc γ‖ = ‖z - pc γ‖ := by
    rw [show (starRingEnd ℂ) z - (pc γ : ℂ) = (starRingEnd ℂ) (z - pc γ) by simp,
      Complex.norm_conj]
  have e2 : ((starRingEnd ℂ) z - pc γ).re = (z - pc γ).re := by simp
  have e3 : ‖1 - (starRingEnd ℂ) z‖ = ‖1 - z‖ := by
    rw [show (1 : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) (1 - z) by simp, Complex.norm_conj]
  have e4 : ∀ j : Fin r, ‖(π j : ℂ) - (starRingEnd ℂ) z‖ = ‖(π j : ℂ) - z‖ := by
    intro j
    rw [show (π j : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) ((π j : ℂ) - z) by simp,
      Complex.norm_conj]
  refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, by rw [e1]; exact h3, by rw [e3]; exact h4,
    fun j hj => by rw [e4]; exact h5 j hj, by rw [re_fFn_conj]; exact h6⟩

theorem dist_of_im {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (z : ℂ) (d : ℝ) (h : d ≤ |z.im|) :
    d ≤ ‖1 - z‖ ∧ ∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - z‖ := by
  refine ⟨?_, fun j _ => ?_⟩
  · have := Complex.abs_im_le_norm (1 - z)
    rw [sub_im, one_im, zero_sub, abs_neg] at this; linarith only [h, this]
  · have := Complex.abs_im_le_norm ((π j : ℂ) - z)
    rw [sub_im, ofReal_im, zero_sub, abs_neg] at this; linarith only [h, this]

theorem omega_conj : exp (((-Real.pi / 3 : ℝ) : ℂ) * I) =
    (starRingEnd ℂ) (exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

theorem sqrt3_bounds : 1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h0 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

theorem good_G1 {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (γ q δ ℓ L κ t : ℝ) (hδ : 0 < δ)
    (hℓL : ℓ ≤ L) (hδℓ : δ ≤ ℓ) (ht : t ∈ Set.uIoc δ ℓ)
    (h1 : AntitoneOn (fun t : ℝ =>
      (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) (Set.Icc δ ℓ))
    (hdec : (fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re -
      (fFn γ q (pc γ)).re ≤ -κ) :
    Good γ q δ L κ k π ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by
  obtain ⟨hωr, hωi, -, -⟩ := omega_re_im
  obtain ⟨hs1, -⟩ := sqrt3_bounds
  rw [Set.uIoc_of_le hδℓ] at ht
  obtain ⟨ht1, ht2⟩ := ht
  have ht0 : 0 < t := by linarith only [hδ, ht1]
  have hn : ‖(pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) - pc γ‖ = t := by
    rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
      Real.norm_of_nonneg ht0.le]
  have hre : ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) - pc γ).re = t / 2 := by
    rw [add_sub_cancel_left, re_ofReal_mul, hωr]; ring
  have him : ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)).im =
      t * (Real.sqrt 3 / 2) := by
    rw [add_im, ofReal_im, im_ofReal_mul, hωi, zero_add]
  have hd : δ / 2 ≤ |((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)).im| := by
    rw [him, abs_of_nonneg (by positivity)]; nlinarith
  obtain ⟨hd1, hd2⟩ := dist_of_im k π _ _ hd
  refine ⟨by rw [hn]; linarith only [ht1], by rw [hre]; linarith only [ht0], by rw [hn]; linarith only [hℓL, ht2], hd1, hd2, ?_⟩
  have := h1 ⟨le_refl δ, hδℓ⟩ ⟨ht1.le, ht2⟩ ht1.le
  simp only at this
  linarith only [hdec, this]

theorem good_G2 {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (γ q δ ℓ L κ R x : ℝ) (hδ : 0 < δ)
    (hδℓ : 2 * δ ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hRL : 1 + R ≤ L) (hR : 0 ≤ R) (hx : x ∈ Set.uIoc 0 R)
    (h1 : AntitoneOn (fun t : ℝ =>
      (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) (Set.Icc δ ℓ))
    (h2 : AntitoneOn (fun x : ℝ =>
      (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))).re)
      (Set.Icc 0 R))
    (hdec : (fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re -
      (fFn γ q (pc γ)).re ≤ -κ) :
    Good γ q δ L κ k π ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) := by
  obtain ⟨hωr, hωi, -, -⟩ := omega_re_im
  obtain ⟨hs1, hs2⟩ := sqrt3_bounds
  rw [Set.uIoc_of_le hR] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hℓ0 : 0 < ℓ := by linarith only [hδ, hδℓ]
  set ω := exp (((Real.pi / 3 : ℝ) : ℂ) * I) with hω
  have hsub : (pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ) - pc γ = (ℓ : ℂ) * ω + (x : ℂ) := by ring
  have hre : ((pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ) - pc γ).re = ℓ / 2 + x := by
    rw [hsub, add_re, re_ofReal_mul, hωr, ofReal_re]; ring
  have him : ((pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ)).im = ℓ * (Real.sqrt 3 / 2) := by
    rw [add_im, add_im, ofReal_im, im_ofReal_mul, hωi, ofReal_im]; ring
  have himp : ((pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ) - pc γ).im = ℓ * (Real.sqrt 3 / 2) := by
    rw [sub_im, him, ofReal_im, sub_zero]
  have hY : δ ≤ ℓ * (Real.sqrt 3 / 2) := by nlinarith
  have hn1 : δ ≤ ‖(pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ) - pc γ‖ := by
    have := Complex.abs_im_le_norm ((pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ) - pc γ)
    rw [himp, abs_of_nonneg (by positivity)] at this; linarith only [hY, this]
  have hn2 : ‖(pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ) - pc γ‖ ≤ L := by
    rw [hsub]
    calc ‖(ℓ : ℂ) * ω + (x : ℂ)‖ ≤ ‖(ℓ : ℂ) * ω‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ = ℓ + x := by
        rw [norm_mul, hω, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real,
          Real.norm_of_nonneg hℓ0.le, Real.norm_of_nonneg hx1.le]
      _ ≤ L := by linarith only [hℓ1, hRL, hx2]
  have hd : δ / 2 ≤ |((pc γ : ℂ) + (ℓ : ℂ) * ω + (x : ℂ)).im| := by
    rw [him, abs_of_nonneg (by positivity)]; linarith only [hδ, hY]
  obtain ⟨hd1, hd2⟩ := dist_of_im k π _ _ hd
  refine ⟨hn1, by rw [hre]; linarith only [hx1, hℓ0], hn2, hd1, hd2, ?_⟩
  have e2 := h2 ⟨le_refl 0, hR⟩ ⟨hx1.le, hx2⟩ hx1.le
  have e1 := h1 ⟨le_refl δ, by linarith only [hδ, hδℓ]⟩ ⟨by linarith only [hδ, hδℓ], le_refl ℓ⟩ (by linarith only [hδ, hδℓ])
  simp only [ofReal_zero, add_zero] at e1 e2
  linarith only [hdec, e1, e2]

theorem good_G3 {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (γ q δ ℓ L κ R P₀ y : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hℓ : ℓ = 2 * (1 - pc γ)) (hℓ1 : ℓ ≤ 1) (hδℓ : δ ≤ ℓ) (hR1 : 1 ≤ R)
    (hRP : P₀ ≤ R) (hRL : 2 + R ≤ L)
    (hπ : ∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀)
    (hy : y ∈ Set.uIoc (-(ℓ * (Real.sqrt 3 / 2))) (ℓ * (Real.sqrt 3 / 2)))
    (h1 : AntitoneOn (fun t : ℝ =>
      (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) (Set.Icc δ ℓ))
    (h3 : ∀ y : ℝ, 0 ≤ y → y ≤ ℓ * (Real.sqrt 3 / 2) →
      (fFn γ q (1 + (R : ℂ) + (y : ℂ) * I)).re ≤
        (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re)
    (hdec : (fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re -
      (fFn γ q (pc γ)).re ≤ -κ) :
    Good γ q δ L κ k π (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) := by
  obtain ⟨hs1, hs2⟩ := sqrt3_bounds
  have hX : pc γ + ℓ / 2 + R = 1 + R := by rw [hℓ]; ring
  have hpc1 : pc γ ≤ 1 := by linarith only [hδ, hℓ, hδℓ]
  have hpc0 : 1 / 2 ≤ pc γ := by linarith only [hℓ, hℓ1]
  have hℓ0 : 0 ≤ ℓ := by linarith only [hX, hpc1]
  have hY : 0 ≤ ℓ * (Real.sqrt 3 / 2) := by positivity
  rw [Set.uIoc_of_le (by linarith only [hY])] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hyabs : |y| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  rw [hX]
  have hre : (((1 + R : ℝ) : ℂ) + (y : ℂ) * I - pc γ).re = 1 + R - pc γ := by simp
  have him : (((1 + R : ℝ) : ℂ) + (y : ℂ) * I - pc γ).im = y := by simp
  have hn1 : 1 + R - pc γ ≤ ‖((1 + R : ℝ) : ℂ) + (y : ℂ) * I - pc γ‖ := by
    have := Complex.re_le_norm (((1 + R : ℝ) : ℂ) + (y : ℂ) * I - pc γ); rwa [hre] at this
  have hn2 : ‖((1 + R : ℝ) : ℂ) + (y : ℂ) * I - pc γ‖ ≤ L := by
    have := Complex.norm_le_abs_re_add_abs_im (((1 + R : ℝ) : ℂ) + (y : ℂ) * I - pc γ)
    rw [hre, him, abs_of_nonneg (by linarith only [hδ, hℓ, hδℓ, hR1])] at this; linarith only [hRL, hpc0, hyabs, this]
  have hd1 : δ / 2 ≤ ‖1 - (((1 + R : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    have := Complex.abs_re_le_norm (1 - (((1 + R : ℝ) : ℂ) + (y : ℂ) * I))
    have e : (1 - (((1 + R : ℝ) : ℂ) + (y : ℂ) * I)).re = -R := by simp
    rw [e, abs_neg, abs_of_nonneg (by linarith only [hR1])] at this; linarith only [hℓ1, hδℓ, hR1, this]
  have hd2 : ∀ j : Fin r, k ≤ (j : ℕ) → δ / 2 ≤ ‖(π j : ℂ) - (((1 + R : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    intro j hj
    obtain ⟨-, hP⟩ := hπ j hj
    have := Complex.abs_re_le_norm ((π j : ℂ) - (((1 + R : ℝ) : ℂ) + (y : ℂ) * I))
    have e : ((π j : ℂ) - (((1 + R : ℝ) : ℂ) + (y : ℂ) * I)).re = π j - (1 + R) := by simp
    rw [e, abs_of_neg (by linarith only [hRP, hP])] at this; linarith only [hℓ1, hδℓ, hRP, hP, this]
  refine ⟨by linarith only [hℓ, hℓ1, hδℓ, hR1, hn1], by rw [hre]; linarith only [hδ, hℓ, hδℓ, hR1], hn2, hd1, hd2, ?_⟩
  have hf : (fFn γ q (((1 + R : ℝ) : ℂ) + (y : ℂ) * I)).re ≤
      (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re := by
    rcases le_or_gt 0 y with hy0 | hy0
    · have := h3 y hy0 hy2
      have e : ((1 + R : ℝ) : ℂ) + (y : ℂ) * I = 1 + (R : ℂ) + (y : ℂ) * I := by push_cast; ring
      rw [e]; exact this
    · have := h3 (-y) (by linarith only [hy0]) (by linarith only [hy1])
      have e : ((1 + R : ℝ) : ℂ) + (y : ℂ) * I =
          (starRingEnd ℂ) (1 + (R : ℂ) + ((-y : ℝ) : ℂ) * I) := by
        rw [map_add, map_add, map_mul, map_one, Complex.conj_ofReal, Complex.conj_ofReal,
          Complex.conj_I]; push_cast; ring
      rw [e, re_fFn_conj]; exact this
  have e1 := h1 ⟨le_refl δ, hδℓ⟩ ⟨hδℓ, le_refl ℓ⟩ hδℓ
  simp only at e1
  linarith only [hdec, hf, e1]

set_option maxHeartbeats 1000000 in
/-- All five far pieces of `Γ*` (BBP (153)-(157), `Γ₁` beyond `δ`, `Γ₂`, `Γ₃` and conjugates). -/
theorem far_all (ε U₀ γ₀ P₀ δ R Nmax : ℝ) (r k : ℕ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hP₀ : 0 ≤ P₀)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / (2 * (γ₀ + 1))) (hR1 : 1 ≤ R) (hRP : P₀ ≤ R) (hN : 0 ≤ Nmax) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q u m σ ℓ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 1 ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) → ℓ = 2 * (1 - pc γ) →
      AntitoneOn (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) (Set.Icc δ ℓ) →
      AntitoneOn (fun x : ℝ => (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))).re)
        (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ ℓ * (Real.sqrt 3 / 2) →
        (fFn γ q (1 + (R : ℂ) + (y : ℂ) * I)).re ≤ (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re - (fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            hH γ q u M k π (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) * I‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, hH γ q u M k π ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, hH γ q u M k π ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, hH γ q u M k π ((pc γ : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, hH γ q u M k π ((pc γ : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) := by
  have hγ01 : (0 : ℝ) < γ₀ + 1 := by linarith only [hγ₀]
  have hδ1' : δ ≤ 1 := by
    have : 1 / (2 * (γ₀ + 1)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith only [hγ₀]
    linarith only [hδ1, this]
  obtain ⟨B, hB0, hB⟩ := far_generic ε U₀ δ (δ ^ 3 / 6) (2 + R) Nmax γ₀ P₀ r k hε hδ hδ1'
    (by positivity) (by linarith only [hR1]) hN hγ₀ hP₀
  refine ⟨B, hB0, ?_⟩
  intro π γ q u m σ ℓ M hu hm1 hm3 hγ1 hγ hν0 hνN hσdef hσ hq hσδ hπ hℓ h1 h2 h3 hdec
  have hγ0 : 0 < γ := by linarith only [hγ1]
  have hℓv : ℓ = 2 / (γ + 1) := by rw [hℓ]; unfold pc; field_simp; ring
  have hℓ1 : ℓ ≤ 1 := by rw [hℓv, div_le_one (by linarith only [hγ0])]; linarith only [hγ1]
  have h2δ : 2 * δ ≤ ℓ := by
    have e1 : 2 * δ ≤ 1 / (γ₀ + 1) := by
      have := mul_le_mul_of_nonneg_left hδ1 (by norm_num : (0 : ℝ) ≤ 2)
      have e : 2 * (1 / (2 * (γ₀ + 1))) = 1 / (γ₀ + 1) := by field_simp
      linarith only [this, e]
    have e2 : 1 / (γ₀ + 1) ≤ ℓ := by
      rw [hℓv, div_le_div_iff₀ hγ01 (by linarith only [hγ0])]; linarith only [hγ, hγ0]
    linarith only [e1, e2]
  have hδℓ : δ ≤ ℓ := by linarith only [hδ, h2δ]
  have hℓ0 : 0 ≤ ℓ := by linarith only [hδ, hδℓ]
  obtain ⟨hs1, hs2⟩ := sqrt3_bounds
  have common := fun (z : ℝ → ℂ) (w : ℂ) (α β : ℝ) (hw : ‖w‖ ≤ 1) (hab : |β - α| ≤ 2 + R)
      (hpt : ∀ s ∈ Set.uIoc α β, Good γ q δ (2 + R) (δ ^ 3 / 6) k π (z s)) =>
    hB π γ q u m σ M z w α β hu hm1 hm3 hγ1 hγ hν0 hνN hσdef hσ hq hσδ hπ hw hab hpt
  have hWn : ‖exp (((Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤ 1 := by rw [norm_exp_ofReal_mul_I]
  have hWbn : ‖exp (((-Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤ 1 := by rw [norm_exp_ofReal_mul_I]
  have hab1 : |ℓ - δ| ≤ 2 + R := by rw [abs_of_nonneg (by linarith only [hδℓ])]; linarith only [hP₀, hδ, hRP, hℓ1]
  have hab2 : |R - 0| ≤ 2 + R := by rw [sub_zero, abs_of_nonneg (by linarith only [hR1])]; linarith only []
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hab3 : |ℓ * (Real.sqrt 3 / 2) - -(ℓ * (Real.sqrt 3 / 2))| ≤ 2 + R := by
      have := mul_nonneg hℓ0 (Real.sqrt_nonneg 3)
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    exact common (fun y => ((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) I _ _
      (by rw [Complex.norm_I]) hab3
      (fun y hy => good_G3 k π γ q δ ℓ (2 + R) (δ ^ 3 / 6) R P₀ y hδ hδ1' hℓ hℓ1 hδℓ hR1 hRP
        (le_refl _) hπ hy h1 h3 hdec)
  · have := common (fun x => (pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) 1 0 R (by rw [norm_one]) hab2
      (fun x hx => good_G2 k π γ q δ ℓ (2 + R) (δ ^ 3 / 6) R x hδ h2δ hℓ1 (by linarith only [])
        (by linarith only [hR1]) hx h1 h2 hdec)
    simpa only [mul_one] using this
  · exact common (fun t => (pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) (exp (((Real.pi / 3 : ℝ) : ℂ) * I)) δ ℓ hWn hab1
      (fun t ht => good_G1 k π γ q δ ℓ (2 + R) (δ ^ 3 / 6) t hδ (by linarith only [hR1, hℓ1]) hδℓ ht h1 hdec)
  · refine common (fun t => (pc γ : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) (exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) δ ℓ hWbn hab1 (fun t ht => ?_)
    have e : (pc γ : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((pc γ : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by
      rw [omega_conj, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    try simp only
    rw [e]
    exact good_conj _ _ _ _ _ _ _ _
      (good_G1 k π γ q δ ℓ (2 + R) (δ ^ 3 / 6) t hδ (by linarith only [hR1, hℓ1]) hδℓ ht h1 hdec)
  · have := common (fun x => (pc γ : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) 1 0 R (by rw [norm_one]) hab2
      (fun x hx => by
        have e : (pc γ : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ) =
            (starRingEnd ℂ) ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) := by
          rw [omega_conj, map_add, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
            Complex.conj_ofReal]
        try simp only
        rw [e]
        exact good_conj _ _ _ _ _ _ _ _
          (good_G2 k π γ q δ ℓ (2 + R) (δ ^ 3 / 6) R x hδ h2δ hℓ1 (by linarith only []) (by linarith only [hR1]) hx
            h1 h2 hdec))
    simpa only [mul_one] using this

end P31F

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε U₀ γ₀ P₀ δ R Nmax : ℝ) (r k : ℕ), 0 < ε → 1 ≤ γ₀ → 0 ≤ P₀ →
    0 < δ → δ ≤ 1 / (2 * (γ₀ + 1)) → 1 ≤ R → P₀ ≤ R → 0 ≤ Nmax →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q u m σ ℓ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 1 ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) → ℓ = 2 * (1 - pc γ) →
      AntitoneOn (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) *
        exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) (Set.Icc δ ℓ) →
      AntitoneOn (fun x : ℝ => (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) *
        exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))).re) (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ ℓ * (Real.sqrt 3 / 2) →
        (fFn γ q (1 + (R : ℂ) + (y : ℂ) * I)).re ≤
          (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re -
        (fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * ((((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) - q)) * exp ((M : ℂ) * fFn γ q (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I)) * (1 / (((pc γ : ℂ) - (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I)) ^ k * gFn k π (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I)))) * I‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) ^ k * gFn k π ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))))‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I))))) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I))))) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) ^ k * gFn k π ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))))‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) := by
  exact P31F.far_all
