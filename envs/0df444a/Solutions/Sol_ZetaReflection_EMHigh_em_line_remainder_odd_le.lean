-- Prove2me | solution 1 for ZetaReflection.EMHigh.em_line_remainder_odd_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:12:22.496282+00:00
-- url     : https://prove2.me/submissions/16da0502-0b0c-4b44-9bca-a615797d0b20

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
import Theorems.Thm_ZetaReflection_EMHigh_em_zeta_orderK_enclosure_odd
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





lemma poch_succ (s : ℂ) (k : ℕ) : poch s (k + 1) = poch s k * (s + k) := rfl

lemma norm_poch_succ (s : ℂ) (k : ℕ) : ‖poch s (k + 1)‖ = ‖poch s k‖ * ‖s + k‖ := by
  rw [poch_succ, norm_mul]











/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/













/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/



theorem norm_poch_sq (σ t : ℝ) (k : ℕ) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ^ 2 = pochNormSq σ t k := by
  induction k with
  | zero => simp [pochNormSq, poch]
  | succ k ih =>
    rw [norm_poch_succ, mul_pow, ih, pochNormSq, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.add_im, Complex.mul_im, Complex.natCast_im]
    ring

theorem norm_poch_le (σ t : ℝ) (k : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : pochNormSq σ t k ≤ Q ^ 2) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ Q := by
  rw [← norm_poch_sq] at hQ
  have h0 := norm_nonneg (poch ((σ : ℂ) + (t : ℂ) * I) k)
  nlinarith [hQ]





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













/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/










theorem solution (K : ℕ) (hK : 1 ≤ K) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) (Q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ : pochNormSq (1 / 2) t (2 * K + 1) ≤ Q ^ 2) (r : ℕ) (hr0 : 0 < r)
    (hr : r ^ 2 ≤ N) :
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - emFinite K ((1 / 2 : ℂ) + (t : ℂ) * I) N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Q
          / ((N : ℝ) ^ (2 * K) * r) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have h := em_zeta_orderK_enclosure_odd K hK hs hs1 hN
  rw [hre] at h
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hm1 : (3 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * K + 1 by omega)
  have hpoch : ‖poch s (2 * K + 1)‖ ≤ Q := by
    have := norm_poch_le (1 / 2) t (2 * K + 1) Q hQ0 hQ
    simpa [hsdef] using this
  have hden : ((1 / 2 : ℝ) + ((2 * K + 1 : ℕ) : ℝ) - 1) = ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 := by ring
  have hdpos : (0 : ℝ) < ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 := by linarith
  have hpow : (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2)) ≤ 1 / ((N : ℝ) ^ (2 * K) * r) := by
    have hsq : (r : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast hr
    have e : (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2))
        = 1 / ((N : ℝ) ^ (2 * K) * Real.sqrt N) := by
      have hk : ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 = ((2 * K : ℕ) : ℝ) + (1 / 2 : ℝ) := by
        push_cast; ring
      rw [hk, Real.rpow_neg (le_of_lt hNR), Real.rpow_add hNR, Real.rpow_natCast,
        ← Real.sqrt_eq_rpow, one_div]
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [hden] at h
  refine le_trans h ?_
  have hpi6 : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by
    have := Real.pi_gt_three
    nlinarith
  have hC : 0 ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) := by positivity
  have hpn : 0 ≤ (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2)) := by positivity
  calc 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
        * (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2)) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2)
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Q
          * (1 / ((N : ℝ) ^ (2 * K) * r)) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2) := by
        gcongr
    _ = 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Q
          / ((N : ℝ) ^ (2 * K) * r) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2) := by ring
