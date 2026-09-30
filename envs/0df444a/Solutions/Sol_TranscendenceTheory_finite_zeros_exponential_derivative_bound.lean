-- Prove2me | solution 1 for TranscendenceTheory.finite_zeros_exponential_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T15:28:51.581386+00:00
-- url     : https://prove2.me/submissions/3e48fd8d-5f1d-4dcb-8526-49a5b87baa4e

import Theorems.Thm_TranscendenceTheory_finite_zeros_derivative_bound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Metric Set
open scoped Topology

open TranscendenceTheory

private lemma factorial_schwarz_decay (α β C K : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, ∀ n E : ℕ, ∀ q : ℝ,
      (n : ℝ) ≤ K * ((N : ℝ) / Real.log N) →
      α * (N : ℝ) ^ 2 ≤ E → 0 ≤ q → q ≤ (N : ℝ) ^ (-β) →
      n.factorial * (Real.exp (C * (N : ℝ) ^ 2) * q ^ E) ≤
        Real.exp (-(α * β / 2) * (N : ℝ) ^ 2 * Real.log N) := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hn
  filter_upwards [hn.eventually (eventually_ge_atTop (2 : ℝ)),
    hlog.eventually_ge_atTop K,
    hlog.eventually_ge_atTop (2 * (C + K) / (α * β))]
    with N hN hlogK hlogC n E q hnE hE hq hqN
  dsimp only [Function.comp_def] at hlogK hlogC
  have hN0 : (0 : ℝ) < N := by linarith only [hN]
  have hlog0 : 0 < Real.log N := Real.log_pos (by linarith only [hN])
  have hnlog : (n : ℝ) * Real.log N ≤ K * N := by
    apply (le_div_iff₀ hlog0).mp
    simpa only [mul_div_assoc] using hnE
  have hnN : (n : ℝ) ≤ N := by
    apply (mul_le_mul_iff_of_pos_right hlog0).mp
    exact hnlog.trans (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hlogK hN0.le)
  have hfact : (n.factorial : ℝ) ≤ Real.exp (K * N) := by
    calc
      _ ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
      _ ≤ (N : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hnN n
      _ = Real.exp ((n : ℝ) * Real.log N) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0, mul_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hnlog
  have hpow : q ^ E ≤ Real.exp (-(α * β) * (N : ℝ) ^ 2 * Real.log N) := by
    calc
      _ ≤ ((N : ℝ) ^ (-β)) ^ E := pow_le_pow_left₀ hq hqN E
      _ = Real.exp (-β * E * Real.log N) := by
        rw [Real.rpow_def_of_pos hN0, ← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hE (mul_nonneg hβ.le hlog0.le)
        nlinarith only [h]
  have hbudget : C * (N : ℝ) ^ 2 + K * N ≤
      (α * β / 2) * (N : ℝ) ^ 2 * Real.log N := by
    have h := (div_le_iff₀ (mul_pos hα hβ)).mp hlogC
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (N : ℝ))
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN]
    have hK2 := mul_le_mul_of_nonneg_left hN2 hK.le
    nlinarith only [h', hK2]
  calc
    _ ≤ Real.exp (K * N) *
        (Real.exp (C * (N : ℝ) ^ 2) *
          Real.exp (-(α * β) * (N : ℝ) ^ 2 * Real.log N)) :=
      mul_le_mul hfact (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _))
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (K * N + C * (N : ℝ) ^ 2 -
        (α * β) * (N : ℝ) ^ 2 * Real.log N) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hbudget])

private lemma first_jet_of_product (f G ψ : ℂ → ℂ) (w : ℂ) (n : ℕ)
    (hf : AnalyticAt ℂ f w) (hψ : AnalyticAt ℂ ψ w)
    (hG : G =ᶠ[𝓝 w] fun z => ψ z * f z)
    (hzero : ∀ j < n, iteratedDeriv j f w = 0) :
    iteratedDeriv n G w = ψ w * iteratedDeriv n f w := by
  rw [hG.iteratedDeriv_eq n, iteratedDeriv_fun_mul hψ.contDiffAt hf.contDiffAt]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have hni : n - i < n := by
      have := Finset.mem_range.mp hi
      omega
    rw [hzero _ hni, mul_zero]
  · simp

/-- Quadratically many zeros yield uniform exponential decay of bounded jets,
including the first surviving jet before multiplication by an analytic factor. -/
theorem solution (α β B K : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hB : 0 ≤ B) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (G : ℂ → ℂ), AnalyticOnNhd ℂ G univ →
      ∀ (s : Finset ℂ) (m : ℂ → ℕ),
        (∀ a ∈ s, ∀ j < m a, iteratedDeriv j G a = 0) →
      ∀ r R : ℝ, 0 < r → r < R →
        (∀ a ∈ s, ‖a‖ ≤ r) →
        α * (N : ℝ) ^ 2 ≤ (∑ a ∈ s, m a : ℕ) →
        2 * r / R ≤ (N : ℝ) ^ (-β) →
        (∀ z ∈ sphere (0 : ℂ) R, ‖G z‖ ≤ Real.exp (B * (N : ℝ) ^ 2)) →
      ∀ (w : ℂ), ‖w‖ + 1 ≤ r →
      ∀ n : ℕ, (n : ℝ) ≤ K * ((N : ℝ) / Real.log N) →
        ‖iteratedDeriv n G w‖ ≤
          Real.exp (-(α * β / 2) * (N : ℝ) ^ 2 * Real.log N) ∧
        ∀ f ψ : ℂ → ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ ψ w →
          G =ᶠ[𝓝 w] (fun z => ψ z * f z) →
          (∀ j < n, iteratedDeriv j f w = 0) → ψ w ≠ 0 →
          ‖ψ w‖⁻¹ ≤ Real.exp (B * (N : ℝ) ^ 2) →
          ‖iteratedDeriv n f w‖ ≤
            Real.exp (-(α * β / 2) * (N : ℝ) ^ 2 * Real.log N) := by
  filter_upwards [factorial_schwarz_decay α β (2 * B) K hα hβ hK]
    with N hN G hG s m hzero r R hr hrR hs hcount hratio houter w hw n hn
  have hR : 0 < R := hr.trans hrR
  have hraw := (finite_zeros_derivative_bound G hG s m hzero r R
    (Real.exp (B * (N : ℝ) ^ 2)) hr hrR hs houter).2 w 1 (by norm_num) hw n
  simp only [one_pow, div_one] at hraw
  have hsmall := hN n (∑ a ∈ s, m a) (2 * r / R) hn hcount (by positivity) hratio
  have hB2 : Real.exp (B * (N : ℝ) ^ 2) ≤ Real.exp (2 * B * (N : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hB (sq_nonneg (N : ℝ))]
  constructor
  · apply hraw.trans
    apply le_trans _ hsmall
    gcongr
  · intro f ψ hf hψ hGf hfirst hψ0 hinv
    have hjet := first_jet_of_product f G ψ w n hf hψ hGf hfirst
    have hnorm : ‖iteratedDeriv n f w‖ = ‖ψ w‖⁻¹ * ‖iteratedDeriv n G w‖ := by
      rw [hjet, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ0), one_mul]
    rw [hnorm]
    apply le_trans (mul_le_mul hinv hraw (norm_nonneg _) (Real.exp_nonneg _))
    calc
      _ = n.factorial * (Real.exp (2 * B * (N : ℝ) ^ 2) *
          (2 * r / R) ^ (∑ a ∈ s, m a)) := by
        have hexp : Real.exp (B * (N : ℝ) ^ 2) * Real.exp (B * (N : ℝ) ^ 2) =
            Real.exp (2 * B * (N : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = n.factorial * ((Real.exp (B * (N : ℝ) ^ 2) *
              Real.exp (B * (N : ℝ) ^ 2)) * (2 * r / R) ^ (∑ a ∈ s, m a)) := by ring
          _ = _ := by rw [hexp]
      _ ≤ _ := hsmall

