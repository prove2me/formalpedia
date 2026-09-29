-- Prove2me | solution 1 for TrigInequalities.sin_pi_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:03:04.731334+00:00
-- url     : https://prove2.me/submissions/b2a26cc6-448c-4f59-8f74-42e29614a1f8

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.ExpSum.Kusmin =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The Kusmin–Landau inequality and van der Corput's second-derivative test

This file develops the B-side foundation of the van der Corput exponential-sum
toolkit: the **Kusmin–Landau inequality** (`kusmin_landau`) and the discrete
**second-derivative test** (`vdC_second_derivative`, milestone 2).

## House note on the character

A concurrent executor is building `Salt/ExpSum/Basic.lean` with an additive
character `eR (x : ℝ) : ℂ := Complex.exp (2πi x)` and its API.  To stay
independent this file defines a **private local copy** `eK` with the *same*
definition.  The house should **unify `eK` with `eR` at wire-in** — every use
of `eK` here is exactly `Complex.exp (2 * π * x * I)`.

## Milestone 1 — Kusmin–Landau

Stated discretely on the consecutive differences `g n := f (n+1) - f n`.

**Mathematical note (a real catch).**  The naive discrete hypothesis
"`Int.fract (g n) ∈ [δ, 1-δ]` and `g` monotone" is *insufficient*: without
pinning `g n` into a *single* unit interval the bound degrades to
`O((b-a)/δ)` (each integer that `g` crosses between samples costs `≍ 1/δ` of
total variation).  In the continuous Kusmin–Landau this cannot happen —
continuity + monotonicity + "bounded away from integers" force `g` to stay in
one interval `(m+δ, m+1-δ)`.  We therefore state the honest discrete shadow:
there is a fixed integer `m` with `g n ∈ [m+δ, m+1-δ]` throughout.  This is
exactly the window that milestone 2's decomposition produces, so the two
milestones are internally consistent.

Result: `‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`  (absolute constant `C = 1`).

The engine is the telescoping weight `w n := (1 - eK (g n))⁻¹`.  Its key
feature (`wK_re`) is that `Re (w n) = 1/2` is *constant*, so the Abel
differences `w (n+1) - w n` are purely imaginary and their total variation
telescopes through `Im (w n) = cot(π · g n)/2`, which is monotone because `g`
is monotone.
-/

namespace Salt.ExpSum

open Real Finset

/-- Private local additive character `eK x = exp(2πi x)`.  **Unify with
`Basic.eR` at wire-in** (identical definition). -/
noncomputable def eK (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

@[simp] lemma eK_norm (x : ℝ) : ‖eK x‖ = 1 := by
  simp only [eK]
  exact Complex.norm_exp_ofReal_mul_I _

lemma eK_add (x y : ℝ) : eK (x + y) = eK x * eK y := by
  simp only [eK, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- Periodicity: `eK` is unchanged by adding an integer. -/
lemma eK_add_intCast (x : ℝ) (k : ℤ) : eK (x + (k : ℝ)) = eK x := by
  have h : (((2 * π * (x + (k : ℝ))) : ℝ) : ℂ) * Complex.I
      = (((2 * π * x : ℝ)) : ℂ) * Complex.I + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  simp only [eK, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `eK` in real cos/sin form. -/
lemma eK_eq (s : ℝ) :
    eK s = (Real.cos (2 * π * s) : ℂ) + (Real.sin (2 * π * s) : ℂ) * Complex.I := by
  simp only [eK, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma eK_re (s : ℝ) : (eK s).re = Real.cos (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma eK_im (s : ℝ) : (eK s).im = Real.sin (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

lemma one_sub_eK_re (s : ℝ) : (1 - eK s).re = 2 * Real.sin (π * s) ^ 2 := by
  have h1 : (1 - eK s).re = 1 - Real.cos (2 * π * s) := by simp [eK_re]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

lemma one_sub_eK_im (s : ℝ) : (1 - eK s).im = -(2 * Real.sin (π * s) * Real.cos (π * s)) := by
  have h1 : (1 - eK s).im = -Real.sin (2 * π * s) := by simp [eK_im]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.sin_two_mul]

lemma normSq_one_sub_eK (s : ℝ) : Complex.normSq (1 - eK s) = 4 * Real.sin (π * s) ^ 2 := by
  rw [Complex.normSq_apply, one_sub_eK_re, one_sub_eK_im]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- Norm of `1 - eK s` as `2|sin(πs)|`. -/
lemma norm_one_sub_eK (s : ℝ) : ‖1 - eK s‖ = 2 * |Real.sin (π * s)| := by
  rw [Complex.norm_def, normSq_one_sub_eK]
  rw [show (4 : ℝ) * Real.sin (π * s) ^ 2 = (2 * |Real.sin (π * s)|) ^ 2 by
        rw [mul_pow]; rw [sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The telescoping weight. -/
noncomputable def wK (s : ℝ) : ℂ := (1 - eK s)⁻¹

/-- `Re (wK s) = 1/2` (constant!) whenever `sin(πs) ≠ 0`. -/
lemma wK_re (s : ℝ) (hs : Real.sin (π * s) ≠ 0) : (wK s).re = 1 / 2 := by
  rw [wK, Complex.inv_re, normSq_one_sub_eK, one_sub_eK_re]
  have : Real.sin (π * s) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-- `Im (wK s) = cos(πs)/(2 sin(πs)) = cot(πs)/2`. -/
lemma wK_im (s : ℝ) (hs : Real.sin (π * s) ≠ 0) :
    (wK s).im = Real.cos (π * s) / (2 * Real.sin (π * s)) := by
  rw [wK, Complex.inv_im, normSq_one_sub_eK, one_sub_eK_im]
  field_simp
  ring

/-- `‖wK s‖ = 1 / (2|sin(πs)|)`. -/
lemma norm_wK (s : ℝ) : ‖wK s‖ = 1 / (2 * |Real.sin (π * s)|) := by
  rw [wK, norm_inv, norm_one_sub_eK, inv_eq_one_div]

/-- `sin(πs) > 0` for `s ∈ (0,1)`. -/
lemma sin_pi_mul_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < Real.sin (π * s) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

/-- Jordan's inequality, symmetrised: `sin(πs) ≥ 2δ` for `s ∈ [δ, 1-δ]`, `δ ≤ 1/2`. -/
lemma sin_pi_mul_ge {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (π * s) := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ≤ Real.sin (π * t) := by
    intro t ht0 ht1
    have hj := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith [Real.pi_pos])
    have hid : 2 / π * (π * t) = 2 * t := by field_simp
    linarith [hid ▸ hj]
  by_cases h : s ≤ 1 / 2
  · exact le_trans (by linarith) (hkey s (by linarith) h)
  · replace h := not_le.mp h
    have hsym : Real.sin (π * s) = Real.sin (π * (1 - s)) := by
      rw [show π * (1 - s) = π - π * s by ring, Real.sin_pi_sub]
    rw [hsym]
    exact le_trans (by linarith) (hkey (1 - s) (by linarith) (by linarith))

/-- Monotonicity of `Im (wK ·) = cot(π ·)/2`: antitone on `(0,1)`. -/
lemma wK_im_antitone {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ < 1) :
    Real.cos (π * s₂) / (2 * Real.sin (π * s₂))
      ≤ Real.cos (π * s₁) / (2 * Real.sin (π * s₁)) := by
  have hs1 : 0 < Real.sin (π * s₁) := sin_pi_mul_pos h1 (lt_of_le_of_lt h12 h2)
  have hs2 : 0 < Real.sin (π * s₂) := sin_pi_mul_pos (lt_of_lt_of_le h1 h12) h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsin : 0 ≤ Real.sin (π * s₂ - π * s₁) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos h1]
  rw [Real.sin_sub] at hsin
  nlinarith [hsin]

/-- A purely imaginary complex number has norm equal to `|Im|`. -/
lemma norm_eq_abs_im_of_re_eq_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  rw [Complex.norm_def, Complex.normSq_apply, h, zero_mul, zero_add, ← sq,
    Real.sqrt_sq_eq_abs]

/-- Abel summation over `range (N+1)`, telescoped form. -/
lemma abel_range (C B : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (N + 1), C k * (B k - B (k + 1))
      = C 0 * B 0 - C N * B (N + 1) + ∑ k ∈ range N, (C (k + 1) - C k) * B (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- **The Kusmin–Landau inequality (discrete form).**

Let `g n := f (n+1) - f n` be the consecutive differences of a phase `f`.
If `g` is monotone (increasing) on `(a, b]` and stays in a single unit
interval bounded away from the integers, `g n ∈ [m + δ, m + 1 - δ]` with
`δ ∈ (0, 1/2]`, then the exponential sum obeys
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`.  The constant is absolute (`C = 1`).

See the file header for why the single-interval hypothesis is essential
(the `Int.fract`-only form is genuinely too weak). -/
theorem kusmin_landau {f : ℕ → ℝ} {a b : ℕ} {δ : ℝ} {m : ℤ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hg_lb : ∀ n, a < n → n ≤ b → (m : ℝ) + δ ≤ f (n + 1) - f n)
    (hg_ub : ∀ n, a < n → n ≤ b → f (n + 1) - f n ≤ (m : ℝ) + 1 - δ)
    (hmono : ∀ n, a < n → n < b → f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ 1 / δ := by
  rcases Nat.lt_or_ge a b with hab | hab
  · -- Main case `a < b`.
    set N : ℕ := b - a - 1 with hNdef
    have hbN : b = a + 1 + N := by omega
    -- reindex `Ioc a b` to `range (N+1)`
    have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range, show b + 1 - (a + 1) = N + 1 by omega]
    -- local sequences
    set σ : ℕ → ℝ := fun k => f (a + 1 + k + 1) - f (a + 1 + k) - (m : ℝ) with hσdef
    set B : ℕ → ℂ := fun k => eK (f (a + 1 + k)) with hBdef
    set W : ℕ → ℂ := fun k => wK (σ k) with hWdef
    -- range facts on `σ`
    have hσ_range : ∀ k, k ≤ N → δ ≤ σ k ∧ σ k ≤ 1 - δ := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k ≤ b := by omega
      have hlb := hg_lb (a + 1 + k) h1 h2
      have hub := hg_ub (a + 1 + k) h1 h2
      simp only [hσdef]; constructor <;> [linarith; linarith]
    have hsin_pos : ∀ k, k ≤ N → 0 < Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_pos (by linarith) (by linarith)
    have hsin_ge : ∀ k, k ≤ N → 2 * δ ≤ Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_ge hδ0 hδ hl hu
    have hσ_mono : ∀ k, k < N → σ k ≤ σ (k + 1) := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k < b := by omega
      have := hmono (a + 1 + k) h1 h2
      simp only [hσdef]
      have he : a + 1 + (k + 1) = a + 1 + k + 1 := by ring
      have he2 : a + 1 + k + 1 + 1 = a + 1 + k + 2 := by ring
      rw [he, he2]; linarith
    -- `Re W = 1/2`, `Im W = cot/2`, monotone, norm-bounded
    have hWre : ∀ k, k ≤ N → (W k).re = 1 / 2 := by
      intro k hk; simp only [hWdef]; exact wK_re _ (ne_of_gt (hsin_pos k hk))
    have hWim : ∀ k, k ≤ N →
        (W k).im = Real.cos (π * σ k) / (2 * Real.sin (π * σ k)) := by
      intro k hk; simp only [hWdef]; exact wK_im _ (ne_of_gt (hsin_pos k hk))
    have hWmono : ∀ k, k < N → (W (k + 1)).im ≤ (W k).im := by
      intro k hk
      rw [hWim (k + 1) (by omega), hWim k (by omega)]
      obtain ⟨hl, _⟩ := hσ_range k (by omega)
      obtain ⟨_, hu⟩ := hσ_range (k + 1) (by omega)
      exact wK_im_antitone (by linarith) (hσ_mono k hk) (by linarith)
    have hWimabs : ∀ k, k ≤ N → |(W k).im| ≤ 1 / (4 * δ) := by
      intro k hk
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [hWim k hk, abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hs) (by positivity)]
      have hcos : |Real.cos (π * σ k)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [hcos, hsg, hδ0,
        mul_le_mul_of_nonneg_right hcos (by positivity : (0 : ℝ) ≤ 4 * δ)]
    have hWnorm : ∀ k, k ≤ N → ‖W k‖ ≤ 1 / (4 * δ) := by
      intro k hk
      simp only [hWdef, norm_wK]
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [abs_of_pos hs]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    -- pointwise Kusmin–Landau identity
    have hid : ∀ k, k ≤ N → W k * (B k - B (k + 1)) = B k := by
      intro k hk
      have hne : 1 - eK (σ k) ≠ 0 := by
        intro hzero
        rw [← norm_eq_zero, norm_one_sub_eK] at hzero
        have hs := hsin_pos k hk
        have : |Real.sin (π * σ k)| = 0 := by linarith [abs_nonneg (Real.sin (π * σ k))]
        rw [abs_eq_zero] at this; linarith
      have hBrec : B (k + 1) = B k * eK (σ k) := by
        simp only [hBdef]
        rw [show f (a + 1 + (k + 1)) = f (a + 1 + k) + (σ k + (m : ℝ)) by
              simp only [hσdef]; ring]
        rw [eK_add, eK_add_intCast]
      rw [hBrec]
      have hfac : B k - B k * eK (σ k) = B k * (1 - eK (σ k)) := by ring
      rw [hfac]
      simp only [hWdef, wK]
      rw [mul_comm (B k) (1 - eK (σ k)), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    -- Abel + triangle inequality
    have hsumeq : ∑ k ∈ Finset.range (N + 1), B k
        = ∑ k ∈ Finset.range (N + 1), W k * (B k - B (k + 1)) :=
      Finset.sum_congr rfl fun k hk => (hid k (by simpa using Finset.mem_range.mp hk)).symm
    have hBnorm : ∀ k, ‖B k‖ = 1 := fun k => by simp only [hBdef]; exact eK_norm _
    rw [hsumeq, abel_range W B N]
    -- variation telescopes to `Im (W 0) - Im (W N)`
    have hvar : ∀ k, k < N → ‖W (k + 1) - W k‖ = (W k).im - (W (k + 1)).im := by
      intro k hk
      have hre : (W (k + 1) - W k).re = 0 := by
        rw [Complex.sub_re, hWre (k + 1) (by omega), hWre k (by omega)]; ring
      rw [norm_eq_abs_im_of_re_eq_zero hre, Complex.sub_im,
        abs_of_nonpos (by linarith [hWmono k hk])]; ring
    have hvarsum : ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ = (W 0).im - (W N).im := by
      rw [Finset.sum_congr rfl fun k hk => hvar k (Finset.mem_range.mp hk)]
      exact Finset.sum_range_sub' (fun k => (W k).im) N
    calc ‖W 0 * B 0 - W N * B (N + 1)
              + ∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖
        ≤ ‖W 0 * B 0 - W N * B (N + 1)‖
            + ‖∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖ := norm_add_le _ _
      _ ≤ (‖W 0 * B 0‖ + ‖W N * B (N + 1)‖)
            + ∑ k ∈ Finset.range N, ‖(W (k + 1) - W k) * B (k + 1)‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = (‖W 0‖ + ‖W N‖) + ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ := by
          simp only [norm_mul, hBnorm, mul_one]
      _ = (‖W 0‖ + ‖W N‖) + ((W 0).im - (W N).im) := by rw [hvarsum]
      _ ≤ (1 / (4 * δ) + 1 / (4 * δ)) + (1 / (4 * δ) + 1 / (4 * δ)) := by
          gcongr
          · exact hWnorm 0 (by omega)
          · exact hWnorm N (by omega)
          · have h0 := le_trans (le_abs_self (W 0).im) (hWimabs 0 (by omega))
            have hN := le_trans (neg_le_abs (W N).im) (hWimabs N (by omega))
            linarith
      _ = 1 / δ := by field_simp; ring
  · -- Empty case `b ≤ a`.
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

/-!
## Milestone 2 — the second-derivative test (RESIDUAL; paper arithmetic recorded)

**Target statement.**  With `g n := f (n+1) - f n`, additionally assume the
second differences obey `λ ≤ g (n+1) - g n ≤ c · λ` for all `n` in range
(`0 < λ`, `1 ≤ c`).  Then, with `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 5 · (c · L · √λ + 1 / √λ)`   (absolute `C' = 5`).

**Paper arithmetic (fully worked; this is the deliverable design).**

Set `δ := √λ`.  Split on the size of `λ`:

* **Case `λ > 1/4`** (so `√λ > 1/2`).  Bound trivially:
  `‖S‖ ≤ #(Ioc a b) = L` (each `‖eK‖ = 1`).  Since `c ≥ 1` and `√λ > 1/2`,
  `L < 2·c·L·√λ ≤ 5·(c L √λ + 1/√λ)`.  ✔

* **Case `λ ≤ 1/4`** (so `δ = √λ ≤ 1/2`, and `λ ≤ 1`).  Because
  `g (n+1) - g n ≥ λ > 0`, `g` is *strictly increasing*.  Decompose
  `Ioc a b` fibrewise by `k := ⌊g n⌋` (`Finset.sum_fiberwise_of_maps_to`):
  each fibre `F_k := {n ∈ Ioc a b : ⌊g n⌋ = k}` is contiguous (`g` mono) and
  the fibres partition the range.  Within `F_k` split by monotonicity into

    - the **good part** `G_k := {n ∈ F_k : g n ∈ [k+δ, k+1-δ]}` — a single
      sub-`Ioc`, so `kusmin_landau` (with this `m := k`) gives
      `‖∑_{G_k} eK (f n)‖ ≤ 1/δ`;
    - the **bad part** `B_k := F_k \ G_k` = `{g n ∈ [k,k+δ) ∪ (k+1-δ,k+1)}`.
      Bound trivially by `#B_k`.  Since `g` increases by `≥ λ` per step, a
      window of `g`-length `w` holds `≤ w/λ + 1` indices, so each of the two
      bad sub-windows (length `δ`) has `≤ δ/λ + 1` indices:
      `#B_k ≤ 2·(δ/λ) + 2`.

  Number of non-empty fibres:
  `K ≤ ⌊g_b⌋ - ⌊g_{a+1}⌋ + 1 ≤ (g_b - g_{a+1}) + 1 ≤ c·λ·L + 1`.

  Summing over the `K` fibres:
  `‖S‖ ≤ K·(1/δ) + K·(2δ/λ + 2) = K·(1/δ + 2δ/λ + 2)`.
  With `δ = √λ`:  `1/δ = 1/√λ`, `2δ/λ = 2/√λ`, so the bracket is
  `3/√λ + 2`, and
  `‖S‖ ≤ (c λ L + 1)·(3/√λ + 2)`
       `= 3 c L √λ + 2 c λ L + 3/√λ + 2`.
  Using `λ ≤ 1` (`⇒ √λ ≤ 1`):  `2 c λ L = 2√λ·(c L √λ) ≤ 2 c L √λ` and
  `2 = 2√λ/√λ ≤ 2/√λ`.  Hence
  `‖S‖ ≤ 5 c L √λ + 5/√λ = 5·(c L √λ + 1/√λ)`.  ✔

Both cases give `C' = 5`.

**Why this is deferred (the real Lean cost).**  The elementary content above
needs three pieces of `Finset` engineering, the middle one being a genuine
sub-obstacle with no mathlib shortcut (see the recon: only the *identity*
predicate has `filter_lt_le_eq_Ioc`):

1.  fibrewise decomposition — available (`Finset.sum_fiberwise_of_maps_to`);
2.  **`G_k` (a monotone-predicate filter of an interval) equals an explicit
    `Finset.Ioc`** — must be built from `StrictMono (g)` by hand; this is a
    C-tier node in its own right and gates the `kusmin_landau` application;
3.  the crossing/window count `#B_k ≤ 2δ/λ + 2` and `K ≤ cλL + 1` from the
    per-step lower bound `g (n+1) - g n ≥ λ`.

`kusmin_landau` (milestone 1) is stated exactly to receive the good windows
`G_k` (single interval `m := k`, `g` increasing), so wiring is mechanical once
(2) lands.  Recorded as the named residual `VK-N2-M2` in `flags.md`.
-/

end Salt.ExpSum

end




section
open Real Finset

theorem solution {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (π * s) := by
  apply Salt.ExpSum.sin_pi_mul_ge <;> assumption

end

