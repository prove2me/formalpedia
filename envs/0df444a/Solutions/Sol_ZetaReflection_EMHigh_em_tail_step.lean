-- Prove2me | solution 1 for ZetaReflection.EMHigh.em_tail_step
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:23.081468+00:00
-- url     : https://prove2.me/submissions/84a65c03-4713-4b2a-9f29-835177688436

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Theorems.Thm_ZetaReflection_EMHigh_emTail_integrableOn
import Theorems.Thm_ZetaReflection_EMHigh_hasDerivAt_emTerm
import Theorems.Thm_ZetaReflection_em_saw_step_window_cpow

/-  EMZetaHigh.lean -- the GENERAL-ORDER Euler-Maclaurin representation of ζ with an explicit,
    PROVED remainder bound (lane emhigh, memo ANDURIL_ARB_DISCHARGE_2026-09-23 section 3 / step 2
    node `AND_em_zeta_orderK`).

    The island's order-3 chain (`EMZetaTail.em_zeta_strip3`) stops at the saw-3 remainder.  This
    file raises the order to ANY `m ≥ 1` by induction, so the finite part carries every Bernoulli
    correction `B_2, B_4, …, B_{2K}` and the remainder decays like `N^{-(Re s + 2K - 1)}`:

      M1.  `poch`, `emC`            -- rising factorial `s(s+1)…(s+k-1)` and the k-th x-derivative
                                       coefficient `(-1)^k (s)_k` of `x^{-s}`.
      M2.  `em_tail_step`           -- ONE saw-order-raising step on the tail `[N, ∞)`, any k ≥ 1
                                       (generalises `EMZetaTail.em_tail2_step` / `em_tail3_step`).
      M3.  `emTail_unroll`          -- the induction: the saw-1 tail equals the explicit Bernoulli
                                       sum plus `(-1)^(m-1) emTail m / m!`.
      M4.  `em_zeta_order`          -- the general-order identity for `riemannZeta` on `Re s > 0`.
      M5.  `emTail_norm_le`         -- remainder bound from any sup bound of the order-m saw.
      M6.  `abs_sawBernoulli_even_le` -- `|B̃_{2K}(x)| ≤ |B_{2K}|` for every K ≥ 1 (Mathlib's
                                       Fourier cosine series of the Bernoulli polynomials).
      M6'. `abs_sawBernoulli_odd_le`  -- `|B̃_{2K+1}(x)| ≤ 2(2K+1)!/(2π)^{2K+1} (1 + (π²/6−1)/2^{2K−1})`
                                       (Fourier sine series + `ζ(p) ≤ 1 + (π²/6−1)/2^{p−2}`).
      M7.  `em_zeta_orderK_enclosure` -- THE THEOREM (general K), even-saw remainder:
             ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)}/(σ+2K-1),
           and `em_zeta_orderK_enclosure_odd`, the same finite part with the saw-(2K+1) remainder
             ‖ζ(s) − emFinite K s N‖ ≤ 2(1+(π²/6−1)/2^{2K−1})/(2π)^{2K+1} · ‖(s)_{2K+1}‖ · N^{-(σ+2K)}/(σ+2K)
           (smaller by about `|s+2K|/(2πN)`), with the evaluator-facing Dirichlet form
           `emFinite = Σ_{n<N} n^{-s} + N^{-s}·emCorr`; `em_line_remainder_le` / `_odd_le` are the
           critical-line forms with a rational majorant `Q` of the Pochhammer norm and `r ≤ √N`.
      M8.  exact Bernoulli numbers `B_2 … B_12` (the K ≤ 6 constants).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin), not a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real Nat

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

section
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
open ZetaReflection.EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/



















/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/








theorem solution (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    emTail s N k
      = (bernoulli (k + 1) : ℂ) * (-(emC s k * ((N : ℝ) : ℂ) ^ (-s - k))) / (k + 1)
        - emTail s N (k + 1) / (k + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set fk : ℝ → ℂ := fun x => emC s k * (x : ℂ) ^ (-s - k) with hfk
  set fk1 : ℝ → ℂ := fun x => emC s (k + 1) * (x : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) with hfk1
  have hIk : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * fk x) (Ioi (N : ℝ)) :=
    emTail_integrableOn k hN (by linarith)
  have hIk1 : IntegrableOn (fun x : ℝ => (sawBernoulli (k + 1) x : ℂ) * fk1 x) (Ioi (N : ℝ)) :=
    emTail_integrableOn (k + 1) hN (by push_cast; linarith)
  -- the finite-window identity for every M ≥ N
  have hwin : ∀ M : ℕ, N ≤ M →
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli k x : ℂ) * fk x)
        = (bernoulliFun (k + 1) 0 : ℂ) * (fk M - fk N) / (k + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    intro M hM
    have hd : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt fk (fk1 x) x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hN) hx.1
      exact hasDerivAt_emTerm hs k (lt_of_lt_of_le zero_lt_one hx1)
    have hi : ∀ j ∈ Finset.Ico N M, IntervalIntegrable fk1 volume (j : ℝ) (j + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_trans hN hj.1
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith)]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      intro x hx
      have : (1 : ℝ) ≤ x := le_trans hj1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
    exact em_saw_step_window_cpow (k := k) hk N M hM fk fk1 hd hi
  -- limits as M → ∞
  have hA : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli k x : ℂ) * fk x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * fk x)) :=
    intervalIntegral_tendsto_integral_Ioi N hIk tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      atTop (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x)) :=
    intervalIntegral_tendsto_integral_Ioi N hIk1 tendsto_natCast_atTop_atTop
  have hEnd0 : Tendsto (fun M : ℕ => fk (M : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun M : ℕ => ‖fk (M : ℝ)‖)
        =ᶠ[atTop] (fun M : ℕ => ‖emC s k‖ * (M : ℝ) ^ (-(s.re + k))) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      rw [hfk, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hMpos]
      congr 2
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
    refine Tendsto.congr' hnorm.symm ?_
    have hz : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(s.re + k))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := s.re + k) (by positivity)).comp tendsto_natCast_atTop_atTop
    simpa using hz.const_mul ‖emC s k‖
  have hRHS : Tendsto (fun M : ℕ =>
      (bernoulliFun (k + 1) 0 : ℂ) * (fk M - fk N) / (k + 1)
        - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1)) atTop
      (𝓝 ((bernoulliFun (k + 1) 0 : ℂ) * (0 - fk N) / (k + 1)
        - (∫ x in Ioi (N : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1))) := by
    apply Tendsto.sub
    · apply Tendsto.div_const
      apply Tendsto.const_mul
      exact hEnd0.sub_const (fk N)
    · exact hB.div_const _
  have hEq : ∀ᶠ M : ℕ in atTop,
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli k x : ℂ) * fk x)
        = (bernoulliFun (k + 1) 0 : ℂ) * (fk M - fk N) / (k + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    filter_upwards [eventually_ge_atTop N] with M hM using hwin M hM
  have hlim := tendsto_nhds_unique (hA.congr' hEq) hRHS
  have hb : (bernoulliFun (k + 1) 0 : ℂ) = (bernoulli (k + 1) : ℂ) := by
    rw [bernoulliFun_eval_zero]; push_cast; rfl
  simp only [emTail]
  rw [hlim, hb, hfk, hfk1]
  push_cast
  ring
