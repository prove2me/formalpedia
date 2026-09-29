-- Prove2me | solution 1 for ZetaBounds.neg_logDeriv_LFunction_trivChar_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T12:43:00.644597+00:00
-- url     : https://prove2.me/submissions/9ec9f649-3355-497c-b785-cc569d297bb2

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.SW.ZetaPole =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, node S3c — the ζ/χ₀ pole bound

Design: `docs/blueprints/sw.md`, wave S3 (the quantitative zero-free region).
This module lands the real-`σ` pole bound that the S3d 3-4-1 assembly consumes:
on `1 < σ ≤ 2`,
```
Re(−ζ'/ζ(σ)) ≤ 1/(σ−1) + 1,        Re(−L'/L(σ, χ₀)) ≤ 1/(σ−1) + 1.
```
The constant is `C₆ = 1`.

## Route (elementary, all at real `σ > 1` via the Dirichlet series)

On `Re s > 1`, mathlib's `LSeries_deriv` gives `−ζ'(σ) = L(↗log)(σ)`, so
`−ζ'/ζ(σ) = L(↗log)(σ) / ζ(σ)` (both real at real `σ`).  We then bound the two
factors by classical sum-vs-integral estimates:

* **`ζ(σ) ≥ 1/(σ−1)`** — `t ↦ t^{−σ}` is antitone, so
  `∫₁^M t^{−σ} dt ≤ Σ_{1≤n<M} n^{−σ} ≤ ζ(σ)`; the left side `→ 1/(σ−1)`.
* **`Σ log n · n^{−σ} ≤ 1/(σ−1)² + 1`** — the summand `log t · t^{−σ}` is
  unimodal, peaking below `e < 3`; split off `n = 2, 3` (which together
  contribute `≤ 1`) and compare the antitone tail `n ≥ 4` with
  `∫₃^∞ log t · t^{−σ} dt ≤ 1/(σ−1)²` (explicit antiderivative
  `−((σ−1)log t + 1) t^{1−σ}/(σ−1)²`).

Combining: `L(↗log)(σ)/ζ(σ) ≤ (1/(σ−1)² + 1)·(σ−1) = 1/(σ−1) + (σ−1) ≤
1/(σ−1) + 1` on `σ ≤ 2`.

The trivial-character version reduces to `ζ` via mathlib's
`LFunctionTrivChar_eq_mul_riemannZeta`: `−L'/L(σ,χ₀) = −ζ'/ζ(σ) − Σ_{p∣q} log p ·
p^{−σ}/(1−p^{−σ})`, and each correction term is a nonnegative real subtracted at
real `σ > 1`.
-/

open scoped LSeries.notation
open Filter Topology MeasureTheory

namespace Salt.SW

/-! ## Real-analysis helpers -/

private lemma zf_antitone {σ : ℝ} (hσ0 : 0 ≤ σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  simp only
  rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ a), Real.rpow_neg (by linarith : (0:ℝ) ≤ b)]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) σ)
    (Real.rpow_le_rpow (by linarith) hab hσ0)

private lemma glogf_antitone {σ : ℝ} (hσ : 1 < σ) :
    AntitoneOn (fun t : ℝ => Real.log t * t ^ (-σ)) (Set.Ici 3) := by
  have hlog3gt1 : (1:ℝ) < Real.log 3 := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num))
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
  · -- ContinuousOn on `Ici 3`
    intro x hx
    simp only [Set.mem_Ici] at hx
    exact ((Real.continuousAt_log (by linarith : x ≠ 0)).mul
      (Real.continuousAt_rpow_const x (-σ) (Or.inl (by linarith)))).continuousWithinAt
  · -- DifferentiableOn on `interior (Ici 3) = Ioi 3`
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : x ≠ 0 := by linarith
    exact ((Real.hasDerivAt_log hx0).mul
      (Real.hasDerivAt_rpow_const (Or.inl hx0))).differentiableAt.differentiableWithinAt
  · -- deriv ≤ 0 on `Ioi 3`
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hxpos : 0 < x := by linarith
    have hd : HasDerivAt (fun t => Real.log t * t ^ (-σ))
        (x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ ((-σ) - 1))) x :=
      (Real.hasDerivAt_log hxpos.ne').mul (Real.hasDerivAt_rpow_const (Or.inl hxpos.ne'))
    rw [hd.deriv]
    have key1 : x⁻¹ * x ^ (-σ) = x ^ ((-σ) - 1) := by
      rw [Real.rpow_sub hxpos, Real.rpow_one, div_eq_mul_inv, mul_comm]
    have hfac : x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ ((-σ) - 1))
        = x ^ ((-σ) - 1) * (1 - σ * Real.log x) := by rw [key1]; ring
    rw [hfac]
    have hpos : 0 < x ^ ((-σ) - 1) := Real.rpow_pos_of_pos hxpos _
    have hlogx : 1 < Real.log x :=
      lt_of_lt_of_le hlog3gt1 (Real.log_le_log (by norm_num) (by linarith))
    have hsig : 1 ≤ σ * Real.log x := by nlinarith [hlogx, hσ]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)

private lemma zf_intervalIntegrable {σ : ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => t ^ (-σ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rcases le_total a b with hab | hab
    · rw [Set.uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge hab] at hx; exact lt_of_lt_of_le hb hx.1
  exact (Real.continuousAt_rpow_const x (-σ) (Or.inl hx0.ne')).continuousWithinAt

private lemma glogf_intervalIntegrable {σ : ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => Real.log t * t ^ (-σ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rcases le_total a b with hab | hab
    · rw [Set.uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge hab] at hx; exact lt_of_lt_of_le hb hx.1
  exact ((Real.continuousAt_log hx0.ne').mul
    (Real.continuousAt_rpow_const x (-σ) (Or.inl hx0.ne'))).continuousWithinAt

/-- The `t^{−σ}` integral over `[1, M]`. -/
private lemma integral_zf {σ : ℝ} (hσ : 1 < σ) (M : ℝ) (hM : 1 ≤ M) :
    ∫ x in (1:ℝ)..M, x ^ (-σ) = M ^ (1 - σ) / (1 - σ) - 1 / (1 - σ) := by
  have h1σ : (1:ℝ) - σ ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) M,
      HasDerivAt (fun t => t ^ (1 - σ) / (1 - σ)) (x ^ (-σ)) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx.1
    have h := (Real.hasDerivAt_rpow_const (x := x) (p := 1 - σ)
      (Or.inl hxpos.ne')).div_const (1 - σ)
    have hval : (1 - σ) * x ^ ((1 - σ) - 1) / (1 - σ) = x ^ (-σ) := by
      rw [show (1 - σ) - 1 = -σ by ring]; field_simp
    rwa [hval] at h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (zf_intervalIntegrable (by norm_num) (by linarith)), Real.one_rpow]

/-- The log-weighted integral over `[1, M]` is at most `1/(σ−1)²`. -/
private lemma integral_glogf_le {σ : ℝ} (hσ : 1 < σ) (M : ℝ) (hM : 1 ≤ M) :
    ∫ x in (1:ℝ)..M, Real.log x * x ^ (-σ) ≤ 1 / (σ - 1) ^ 2 := by
  have hσ1 : σ - 1 ≠ 0 := by linarith
  let F : ℝ → ℝ := fun t => (-(((σ - 1) * Real.log t + 1) * t ^ (1 - σ))) / (σ - 1) ^ 2
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) M, HasDerivAt F (Real.log x * x ^ (-σ)) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx.1
    have hu : HasDerivAt (fun t => (σ - 1) * Real.log t + 1) ((σ - 1) * x⁻¹) x :=
      ((Real.hasDerivAt_log hxpos.ne').const_mul (σ - 1)).add_const 1
    have hv : HasDerivAt (fun t : ℝ => t ^ (1 - σ)) ((1 - σ) * x ^ ((1 - σ) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')
    have hdiv := (((hu.mul hv).neg).div_const ((σ - 1) ^ 2))
    have hpow : x ^ (1 - σ) = x * x ^ (-σ) := by
      rw [Real.rpow_sub hxpos, Real.rpow_one, Real.rpow_neg hxpos.le, div_eq_mul_inv]
    have hval : (-((σ - 1) * x⁻¹ * x ^ (1 - σ)
          + ((σ - 1) * Real.log x + 1) * ((1 - σ) * x ^ ((1 - σ) - 1)))) / (σ - 1) ^ 2
        = Real.log x * x ^ (-σ) := by
      rw [show (1 - σ) - 1 = -σ by ring, hpow]
      field_simp
      ring
    rw [hval] at hdiv
    exact hdiv
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (glogf_intervalIntegrable (by norm_num) (by linarith))
  rw [hFTC]
  have hF1 : F 1 = -(1 / (σ - 1) ^ 2) := by
    change (-(((σ - 1) * Real.log 1 + 1) * (1:ℝ) ^ (1 - σ))) / (σ - 1) ^ 2 = -(1 / (σ - 1) ^ 2)
    rw [Real.log_one, Real.one_rpow]; ring
  have hFM : F M ≤ 0 := by
    change (-(((σ - 1) * Real.log M + 1) * M ^ (1 - σ))) / (σ - 1) ^ 2 ≤ 0
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [neg_nonpos]
    have hnn : 0 ≤ (σ - 1) * Real.log M + 1 := by nlinarith [Real.log_nonneg hM]
    exact mul_nonneg hnn (Real.rpow_pos_of_pos (by linarith) _).le
  rw [hF1]; linarith

/-! ## Term-level bridges between the complex L-series and real series -/

/-- The `n`-th term of `ζ` at real `σ` is the real `1/n^σ`. -/
private lemma ofReal_zeta_term (n : ℕ) (σ : ℝ) :
    ((((n : ℝ) ^ (-σ)) : ℝ) : ℂ) = 1 / (n : ℂ) ^ (σ : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
    Complex.cpow_neg, ← one_div]

/-- The `n`-th term of `L(↗log)` at real `σ` is the real `log n · n^{−σ}`. -/
private lemma term_log_eq (n : ℕ) (σ : ℝ) :
    LSeries.term (↗Complex.log) (σ : ℂ) n = ((Real.log (n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries.term_def₀ (by simp) (σ : ℂ) n, Complex.ofReal_mul, ← Complex.natCast_log]
  congr 1
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg]

/-! ## The ζ pole bound -/

/-- **S3c, the ζ half.** On `1 < σ ≤ 2`,
`Re(−ζ'/ζ(σ)) ≤ 1/(σ−1) + 1`. -/
theorem neg_logDeriv_zeta_le {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + 1 := by
  have hσC : (1 : ℝ) < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact h1
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hp : 0 < σ - 1 := by linarith
  -- Real ζ-series `Z` and its representation / lower bound.
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-σ) with hZ_def
  have hZsummable : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    have : (fun n : ℕ => (n : ℝ) ^ (-σ)) = (fun n : ℕ => 1 / (n : ℝ) ^ σ) := by
      funext n; rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
    rw [this]; exact Real.summable_one_div_nat_rpow.mpr h1
  have hzeta : riemannZeta (σ : ℂ) = (Z : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hσC, hZ_def, Complex.ofReal_tsum]
    exact tsum_congr (fun n => (ofReal_zeta_term n σ).symm)
  have hZlb : 1 / (σ - 1) ≤ Z := by
    have key : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ^ (1 - σ) / (1 - σ) - 1 / (1 - σ) ≤ Z := by
      intro M hM
      have hle : ∫ x in (1:ℝ)..(M : ℝ), x ^ (-σ) ≤ ∑ k ∈ Finset.Ico 1 M, ((k : ℝ)) ^ (-σ) := by
        have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc (↑(1 : ℕ)) (↑M)) :=
          (zf_antitone hσ0).mono (by rw [Nat.cast_one]; exact Set.Icc_subset_Ici_self)
        have := AntitoneOn.integral_le_sum_Ico hM hanti
        rwa [Nat.cast_one] at this
      have hsum : ∑ k ∈ Finset.Ico 1 M, ((k : ℝ)) ^ (-σ) ≤ Z :=
        Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hZsummable
      rw [integral_zf h1 (M : ℝ) (by exact_mod_cast hM)] at hle
      linarith
    have htend0 : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 - σ)) atTop (𝓝 0) := by
      have hrw : (fun M : ℕ => (M : ℝ) ^ (1 - σ)) = (fun M : ℕ => (M : ℝ) ^ (-(σ - 1))) := by
        funext M; rw [show (1:ℝ) - σ = -(σ - 1) by ring]
      rw [hrw]
      exact (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
    have h1σ : (1 : ℝ) - σ ≠ 0 := by linarith
    have hσ1' : σ - 1 ≠ 0 := by linarith
    have htend : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 - σ) / (1 - σ) - 1 / (1 - σ)) atTop
        (𝓝 (1 / (σ - 1))) := by
      have h := (htend0.div_const (1 - σ)).sub_const (1 / (1 - σ))
      have heq : (0 : ℝ) / (1 - σ) - 1 / (1 - σ) = 1 / (σ - 1) := by field_simp; ring
      rwa [heq] at h
    exact le_of_tendsto htend (by filter_upwards [eventually_ge_atTop 1] with M hM using key M hM)
  have hZpos : 0 < Z := lt_of_lt_of_le (one_div_pos.mpr hp) hZlb
  -- Real log-series `Slog` and its upper bound.
  set g : ℕ → ℝ := fun n => Real.log (n : ℝ) * (n : ℝ) ^ (-σ) with hg_def
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n; rw [hg_def]
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hLSS : LSeriesSummable (↗Complex.log) (σ : ℂ) := by
    have h := LSeriesSummable_logMul_of_lt_re (f := (1 : ℕ → ℂ)) (s := (σ : ℂ))
      (by rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast h1)
    have heq : LSeries.logMul (1 : ℕ → ℂ) = ↗Complex.log := by
      funext n; simp [LSeries.logMul]
    rwa [heq] at h
  have hg_summable : Summable g := by
    rw [← Complex.summable_ofReal]
    exact Summable.congr hLSS (fun n => term_log_eq n σ)
  set Slog : ℝ := ∑' n, g n with hSlog_def
  have hlog_eq : LSeries (↗Complex.log) (σ : ℂ) = (Slog : ℂ) := by
    change ∑' n, LSeries.term (↗Complex.log) (σ : ℂ) n = (Slog : ℂ)
    rw [hSlog_def, Complex.ofReal_tsum]
    exact tsum_congr (fun n => term_log_eq n σ)
  -- Tail bound via the antitone comparison.
  have htail : ∑' n : ℕ, g (n + 4) ≤ 1 / (σ - 1) ^ 2 := by
    apply Real.tsum_le_of_sum_range_le (fun i => hg_nonneg _)
    intro N
    have hcmp := AntitoneOn.sum_le_integral (x₀ := (3 : ℝ)) (a := N)
      (f := fun t => Real.log t * t ^ (-σ))
      ((glogf_antitone h1).mono (by
        intro y hy; simp only [Set.mem_Icc] at hy; exact Set.mem_Ici.mpr hy.1))
    have hL : ∀ i : ℕ, (fun t => Real.log t * t ^ (-σ)) ((3 : ℝ) + ↑(i + 1)) = g (i + 4) := by
      intro i
      have hcast : (3 : ℝ) + ↑(i + 1) = ↑(i + 4) := by push_cast; ring
      simp only [hg_def, hcast]
    have hI : ∫ t in (3:ℝ)..(3 + ↑N), Real.log t * t ^ (-σ) ≤ 1 / (σ - 1) ^ 2 := by
      have hsplit : ∫ t in (1:ℝ)..(3 + ↑N), Real.log t * t ^ (-σ)
          = (∫ t in (1:ℝ)..(3:ℝ), Real.log t * t ^ (-σ))
            + ∫ t in (3:ℝ)..(3 + ↑N), Real.log t * t ^ (-σ) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (glogf_intervalIntegrable (by norm_num) (by norm_num))
          (glogf_intervalIntegrable (by norm_num) (by positivity))).symm
      have hnn13 : 0 ≤ ∫ t in (1:ℝ)..(3:ℝ), Real.log t * t ^ (-σ) := by
        apply intervalIntegral.integral_nonneg (by norm_num)
        intro t ht
        simp only [Set.mem_Icc] at ht
        exact mul_nonneg (Real.log_nonneg ht.1) (Real.rpow_nonneg (by linarith) _)
      have hbig := integral_glogf_le h1 (3 + ↑N) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      linarith
    calc ∑ i ∈ Finset.range N, g (i + 4)
        = ∑ i ∈ Finset.range N, (fun t => Real.log t * t ^ (-σ)) ((3 : ℝ) + ↑(i + 1)) :=
          Finset.sum_congr rfl (fun i _ => (hL i).symm)
      _ ≤ ∫ t in (3:ℝ)..(3 + ↑N), Real.log t * t ^ (-σ) := hcmp
      _ ≤ 1 / (σ - 1) ^ 2 := hI
  -- Split off the first four terms; `g 0 = g 1 = 0`, `g 2 + g 3 ≤ 1`.
  have hg23 : g 2 + g 3 ≤ 1 := by
    have hg2 : g 2 ≤ 1 / 2 := by
      rw [hg_def]
      have h2p : (2 : ℝ) ^ (-σ) ≤ 1 / 2 := by
        rw [show (1:ℝ)/2 = (2:ℝ) ^ (-1:ℝ) by rw [Real.rpow_neg_one]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have hl2 : Real.log ((2:ℕ) : ℝ) ≤ 1 := by
        rw [Nat.cast_ofNat]; linarith [Real.log_two_lt_d9]
      have hlnn : 0 ≤ Real.log ((2:ℕ) : ℝ) := Real.log_natCast_nonneg 2
      have hrnn : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
      calc Real.log ((2:ℕ) : ℝ) * ((2:ℕ) : ℝ) ^ (-σ)
          = Real.log ((2:ℕ) : ℝ) * (2 : ℝ) ^ (-σ) := by rw [Nat.cast_ofNat]
        _ ≤ 1 * (1 / 2) := by
            apply mul_le_mul hl2 h2p hrnn (by norm_num)
        _ = 1 / 2 := by ring
    have hg3 : g 3 ≤ 1 / 2 := by
      rw [hg_def]
      have h3p : (3 : ℝ) ^ (-σ) ≤ 1 / 3 := by
        rw [show (1:ℝ)/3 = (3:ℝ) ^ (-1:ℝ) by rw [Real.rpow_neg_one]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have hlog3 : Real.log ((3:ℕ) : ℝ) ≤ 2 * Real.log 2 := by
        rw [Nat.cast_ofNat, show (2:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ (2:ℕ)) by
          rw [Real.log_pow]; push_cast; ring]
        exact Real.log_le_log (by norm_num) (by norm_num)
      have hlnn : 0 ≤ Real.log ((3:ℕ) : ℝ) := Real.log_natCast_nonneg 3
      have hrnn : 0 ≤ (3 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
      calc Real.log ((3:ℕ) : ℝ) * ((3:ℕ) : ℝ) ^ (-σ)
          = Real.log ((3:ℕ) : ℝ) * (3 : ℝ) ^ (-σ) := by rw [Nat.cast_ofNat]
        _ ≤ (2 * Real.log 2) * (1 / 3) := by
            apply mul_le_mul hlog3 h3p hrnn (by positivity)
        _ ≤ 1 / 2 := by nlinarith [Real.log_two_lt_d9]
    linarith
  have hSlog : Slog ≤ 1 / (σ - 1) ^ 2 + 1 := by
    have hsplit : Slog = (∑ i ∈ Finset.range 4, g i) + ∑' n, g (n + 4) := by
      rw [hSlog_def]; exact (Summable.sum_add_tsum_nat_add 4 hg_summable).symm
    have hg0 : g 0 = 0 := by rw [hg_def]; simp [Real.log_zero]
    have hg1 : g 1 = 0 := by rw [hg_def]; simp [Real.log_one]
    have hsum4 : (∑ i ∈ Finset.range 4, g i) = g 2 + g 3 := by
      simp [Finset.sum_range_succ, hg0, hg1]
    rw [hsplit, hsum4]
    linarith [htail, hg23]
  -- Assemble.
  have hval : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re = Slog / Z := by
    have hderiv : -deriv riemannZeta (σ : ℂ) = (Slog : ℂ) := by
      have hz_eq : deriv riemannZeta (σ : ℂ) = deriv (LSeries (1 : ℕ → ℂ)) (σ : ℂ) := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσC] with z hz
        exact (LSeries_one_eq_riemannZeta hz).symm
      rw [hz_eq, LSeries_deriv (by rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast h1), neg_neg]
      rw [show LSeries.logMul (1 : ℕ → ℂ) = ↗Complex.log by funext n; simp [LSeries.logMul]]
      exact hlog_eq
    rw [hderiv, hzeta, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hval]
  -- `Slog / Z ≤ 1/(σ−1) + 1`.
  have hZinv : 1 / Z ≤ σ - 1 := by
    rw [div_le_iff₀ hZpos]
    have h := mul_le_mul_of_nonneg_left hZlb hp.le
    rwa [mul_one_div, div_self hp.ne'] at h
  calc Slog / Z = Slog * (1 / Z) := by rw [mul_one_div]
    _ ≤ (1 / (σ - 1) ^ 2 + 1) * (σ - 1) := by
        exact mul_le_mul hSlog hZinv (one_div_nonneg.mpr hZpos.le) (by positivity)
    _ = 1 / (σ - 1) + (σ - 1) := by field_simp
    _ ≤ 1 / (σ - 1) + 1 := by linarith

/-! ## The trivial-character pole bound -/

/-- **S3c, the χ₀ half.** For `q ≠ 0` and `1 < σ ≤ 2`,
`Re(−L'/L(σ, χ₀)) ≤ 1/(σ−1) + 1`, where `χ₀ = (1 : DirichletCharacter ℂ q)`.
Via `LFunctionTrivChar_eq_mul_riemannZeta`, `L(s, χ₀) = P(s)·ζ(s)` near `σ` with
`P(s) = ∏_{p∣q}(1−p^{−s})`; the Euler correction `logDeriv P σ` is a nonnegative
real, so the bound reduces to `neg_logDeriv_zeta_le`. -/
theorem neg_logDeriv_LFunction_trivChar_le (q : ℕ) [NeZero q] {σ : ℝ}
    (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re
      ≤ 1 / (σ - 1) + 1 := by
  have hσC : (1 : ℝ) < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact h1
  have hσ1 : (σ : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [Complex.ofReal_re, Complex.one_re] at this; linarith
  -- Per-prime real facts: `0 < p^{−σ} < 1`, and the complex factor is a real cast.
  have hrp : ∀ p ∈ q.primeFactors, (0 : ℝ) < (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) < 1 := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    exact ⟨Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p)) _,
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)⟩
  have hpcpow : ∀ p ∈ q.primeFactors,
      (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro p hp
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (by positivity)]
  have hfac_ne : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(σ : ℂ))) ≠ 0 := by
    intro p hp
    rw [hpcpow p hp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    exact ne_of_gt (by linarith [(hrp p hp).2])
  have hp_ne : ∀ p ∈ q.primeFactors, (p : ℂ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
  set P : ℂ → ℂ := fun s => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) with hP_def
  have hP0 : P (σ : ℂ) ≠ 0 := by rw [hP_def]; exact Finset.prod_ne_zero_iff.mpr hfac_ne
  have hζ0 : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hσC
  have hfac_diff : ∀ p ∈ q.primeFactors,
      DifferentiableAt ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ) := fun p hp =>
    (differentiableAt_const 1).sub ((differentiableAt_id.neg).const_cpow (Or.inl (hp_ne p hp)))
  have hPdiff : DifferentiableAt ℂ P (σ : ℂ) := by
    rw [hP_def]; exact DifferentiableAt.fun_finsetProd hfac_diff
  have hζdiff : DifferentiableAt ℂ riemannZeta (σ : ℂ) := differentiableAt_riemannZeta hσ1
  -- Split the logarithmic derivative: `logDeriv L = logDeriv P + logDeriv ζ` near `σ`.
  have hLmul : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
      = logDeriv P (σ : ℂ) + logDeriv riemannZeta (σ : ℂ) := by
    have hEq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 (σ : ℂ)]
        fun s => P s * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hσ1] with s hs
      rw [hP_def]
      exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by simpa using hs)
    have hcong : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
        = logDeriv (fun s => P s * riemannZeta s) (σ : ℂ) := by
      simp only [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
    rw [hcong, logDeriv_mul (σ : ℂ) hP0 hζ0 hPdiff hζdiff]
  -- The Euler correction `logDeriv P σ` is a nonnegative real.
  have hPfacval : ∀ p ∈ q.primeFactors,
      logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ)
        = ((Real.log p * (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    intro p hp
    have hg : HasDerivAt (fun s : ℂ => -s) (-1 : ℂ) (σ : ℂ) := (hasDerivAt_id (σ : ℂ)).neg
    have hcp : HasDerivAt (fun s : ℂ => (p : ℂ) ^ (-s))
        ((p : ℂ) ^ (-(σ : ℂ)) * Complex.log p * (-1)) (σ : ℂ) :=
      hg.const_cpow (Or.inl (hp_ne p hp))
    have hfp : HasDerivAt (fun s : ℂ => 1 - (p : ℂ) ^ (-s))
        (Complex.log p * (p : ℂ) ^ (-(σ : ℂ))) (σ : ℂ) := by
      have h := hcp.const_sub 1
      rw [show -((p : ℂ) ^ (-(σ : ℂ)) * Complex.log p * (-1))
        = Complex.log p * (p : ℂ) ^ (-(σ : ℂ)) by ring] at h
      exact h
    rw [logDeriv_apply, hfp.deriv, hpcpow p hp, ← Complex.natCast_log, ← Complex.ofReal_mul,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div]
  have hPre : 0 ≤ (logDeriv P (σ : ℂ)).re := by
    have hsum : logDeriv P (σ : ℂ)
        = ∑ p ∈ q.primeFactors, logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ) := by
      rw [hP_def]; exact logDeriv_prod hfac_ne hfac_diff
    rw [hsum, Complex.re_sum]
    refine Finset.sum_nonneg (fun p hp => ?_)
    rw [hPfacval p hp, Complex.ofReal_re]
    exact div_nonneg
      (mul_nonneg (Real.log_natCast_nonneg p) (Real.rpow_nonneg (by positivity) _))
      (by linarith [(hrp p hp).2])
  -- Assemble: reduce to the ζ bound plus the nonnegative correction.
  have hζbound : (-(logDeriv riemannZeta (σ : ℂ))).re ≤ 1 / (σ - 1) + 1 := by
    rw [logDeriv_apply, ← neg_div]
    exact neg_logDeriv_zeta_le h1 h2
  rw [hLmul, neg_add, Complex.add_re]
  have hPneg : (-(logDeriv P (σ : ℂ))).re ≤ 0 := by rw [Complex.neg_re]; linarith [hPre]
  linarith [hζbound, hPneg]

end Salt.SW

end




theorem solution (q : ℕ) [NeZero q] {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re
      ≤ 1 / (σ - 1) + 1 :=
  Salt.SW.neg_logDeriv_LFunction_trivChar_le q h1 h2

