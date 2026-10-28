-- Prove2me | solution 1 for ZetaReflection.EMHigh.em_zeta_orderK_enclosure_odd
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:09:36.191889+00:00
-- url     : https://prove2.me/submissions/2f791bed-5961-4f67-a504-f241e2879de8

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
import Theorems.Thm_ZetaReflection_EMHigh_abs_bernoulliFun_odd_le
import Theorems.Thm_ZetaReflection_EMHigh_emFinite_eq_emFiniteM
import Theorems.Thm_ZetaReflection_EMHigh_em_zeta_order
import Theorems.Thm_ZetaReflection_em_tail_integral_bound
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

namespace ZetaReflection

namespace EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/













lemma norm_emC (s : ℂ) (k : ℕ) : ‖emC s k‖ = ‖poch s k‖ := by
  simp [emC, norm_pow]





/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/

/-- `‖emTail s N m‖ ≤ B · ‖(s)_m‖ · N^{-(σ+m-1)} / (σ+m-1)` whenever `|B̃_m| ≤ B`. -/
theorem emTail_norm_le (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N)
    {B : ℝ} (hB0 : 0 ≤ B) (hsaw : ∀ x : ℝ, |sawBernoulli m x| ≤ B) :
    ‖emTail s N m‖ ≤ B * ‖poch s m‖ * (N : ℝ) ^ (-(s.re + m - 1)) / (s.re + m - 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := em_tail_integral_bound (k := m) (s := s) (c := emC s m) (B := B) (N := N) hN
    (by linarith) hB0 hsaw
  rw [norm_emC] at h
  exact h

/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/





/-- **The odd saw sup bound**, all real `x`, `K ≥ 1`. -/
theorem abs_sawBernoulli_odd_le (K : ℕ) (hK : K ≠ 0) (x : ℝ) :
    |sawBernoulli (2 * K + 1) x|
      ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) :=
  abs_bernoulliFun_odd_le K hK ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/









/-- The order-(2K+1) finite part does not change when the saw-(2K+1) remainder form is used: the
    extra Bernoulli term carries `B_{2K+1} = 0`. -/
theorem emFiniteM_odd_eq (K : ℕ) (hK : 1 ≤ K) (s : ℂ) (N : ℕ) :
    emFiniteM (2 * K + 1) s N = emFiniteM (2 * K) s N := by
  simp only [emFiniteM]
  rw [show 2 * K + 1 - 1 = (2 * K - 1) + 1 by omega, Finset.sum_range_succ,
    show 2 * K - 1 + 2 = 2 * K + 1 by omega,
    bernoulli_eq_zero_of_odd (by exact ⟨K, rfl⟩ : Odd (2 * K + 1)) (by omega)]
  simp



/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/











/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/













/-! ## M8. The exact Bernoulli numbers `B_2 … B_12` (the constants of K ≤ 6). -/






















end EMHigh

end ZetaReflection


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









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/












theorem solution (K : ℕ) (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 * K + 1 := by omega
  have hid := em_zeta_order (2 * K + 1) hm hs hs1 hN
  rw [emFinite_eq_emFiniteM K s hN, ← emFiniteM_odd_eq K hK s N]
  have hdiff : riemannZeta s - emFiniteM (2 * K + 1) s N
      = (-1) ^ (2 * K + 1 - 1) * emTail s N (2 * K + 1) / ((2 * K + 1)! : ℂ) := by
    rw [hid]; ring
  rw [hdiff]
  have hF : (0 : ℝ) < ((2 * K + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnorm : ‖(-1) ^ (2 * K + 1 - 1) * emTail s N (2 * K + 1) / ((2 * K + 1)! : ℂ)‖
      = ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    congr 1
    exact_mod_cast Complex.norm_natCast _
  rw [hnorm]
  have hB0 : 0 ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1)
      * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
    have hpi6 : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by
      have := Real.pi_gt_three
      nlinarith
    positivity
  have hbd := emTail_norm_le (2 * K + 1) hm hs hN hB0 (abs_sawBernoulli_odd_le K (by omega))
  have hσ : 0 < s.re + ((2 * K + 1 : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  calc ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ)
      ≤ (2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
          / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / ((2 * K + 1)! : ℝ) :=
        div_le_div_of_nonneg_right hbd hF.le
    _ = _ := by field_simp
