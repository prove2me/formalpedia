-- Prove2me | solution 1 for ZetaReflection.EMHigh.emCorr_re_im
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:50:45.584086+00:00
-- url     : https://prove2.me/submissions/8a3ef37e-f197-4aa2-98ba-1a2f99f1de5c

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













/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/













/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/











/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/



theorem poch_re_im (σ t : ℝ) (k : ℕ) :
    (poch ((σ : ℂ) + (t : ℂ) * I) k).re = (pochRI σ t k).1 ∧
    (poch ((σ : ℂ) + (t : ℂ) * I) k).im = (pochRI σ t k).2 := by
  induction k with
  | zero => simp [pochRI, poch]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [poch_succ, pochRI, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.natCast_im, h1, h2]
    constructor <;> ring





/-- A complex number times a real scalar, real and imaginary parts. -/
private lemma re_im_ofReal_mul (a : ℝ) (z : ℂ) :
    ((a : ℂ) * z).re = a * z.re ∧ ((a : ℂ) * z).im = a * z.im := by
  constructor <;> simp [Complex.mul_re, Complex.mul_im]



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











/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/











theorem solution (K : ℕ) (σ t : ℝ) (N : ℕ) :
    (emCorr K ((σ : ℂ) + (t : ℂ) * I) N).re = emCorrRe K σ t N ∧
    (emCorr K ((σ : ℂ) + (t : ℂ) * I) N).im = emCorrIm K σ t N := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  -- the N/(s-1) part
  have hq : (N : ℂ) / (s - 1)
      = (((N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ)
        + ((-((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
    by_cases h0 : (σ - 1) ^ 2 + t ^ 2 = 0
    · have hσ : σ - 1 = 0 := by nlinarith [sq_nonneg (σ - 1), sq_nonneg t]
      have ht : t = 0 := by nlinarith [sq_nonneg (σ - 1), sq_nonneg t]
      have hs1 : s - 1 = 0 := by
        rw [hsdef, ht]; push_cast
        have : (σ : ℂ) = 1 := by
          have : σ = 1 := by linarith
          rw [this]; simp
        rw [this]; ring
      rw [hs1, div_zero, h0]; simp
    · have hs1 : s - 1 ≠ 0 := by
        intro h
        apply h0
        have hre := congrArg Complex.re h
        have him := congrArg Complex.im h
        simp [hsdef] at hre him
        rw [him]; nlinarith [hre]
      rw [div_eq_iff hs1]
      apply Complex.ext <;>
        simp only [hsdef, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im] <;>
        field_simp <;> ring
  -- each correction term is a real scalar times poch
  have hterm : ∀ i : ℕ, (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)
      = (((bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) : ℝ) : ℂ) * poch s (i + 1) := by
    intro i; push_cast; ring
  have hsum_re : (∑ i ∈ Finset.range (2 * K - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1)
        / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)).re
      = ∑ i ∈ Finset.range (2 * K - 1),
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).1 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm i, (re_im_ofReal_mul _ _).1, (poch_re_im σ t (i + 1)).1]
  have hsum_im : (∑ i ∈ Finset.range (2 * K - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1)
        / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)).im
      = ∑ i ∈ Finset.range (2 * K - 1),
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).2 := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm i, (re_im_ofReal_mul _ _).2, (poch_re_im σ t (i + 1)).2]
  have hre1 : ((((N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ)
        + ((-((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ) * I).re
      = (N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have him1 : ((((N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ)
        + ((-((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ) * I).im
      = -((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) := by
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have hhalf_re : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hhalf_im : ((1 : ℂ) / 2).im = 0 := by norm_num
  constructor
  · rw [emCorr, Complex.add_re, Complex.add_re, hq, hsum_re, emCorrRe, hre1, hhalf_re]
  · rw [emCorr, Complex.add_im, Complex.add_im, hq, hsum_im, emCorrIm, him1, hhalf_im, add_zero]
