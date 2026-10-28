-- Prove2me | solution 1 for ZetaReflection.EMHigh.emTail_unroll_step
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:01:26.152052+00:00
-- url     : https://prove2.me/submissions/f0a999d5-4bc7-4cf2-9b40-2203f4099f59

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
import Theorems.Thm_ZetaReflection_EMHigh_em_tail_step

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


theorem solution {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    (-1) ^ j * emTail s N (j + 1) / ((j + 1)! : ℂ)
      = (bernoulli (j + 2) : ℂ) * poch s (j + 1) / ((j + 2)! : ℂ)
            * ((N : ℝ) : ℂ) ^ (-s - ((j + 1 : ℕ) : ℂ))
        + (-1) ^ (j + 1) * emTail s N (j + 2) / ((j + 2)! : ℂ) := by
  rw [em_tail_step (j + 1) (by omega) hs hN]
  have hf : ((j + 2)! : ℂ) = ((j : ℂ) + 2) * ((j + 1)! : ℂ) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ (j + 1)]; push_cast; ring
  rw [hf]
  have h1 : ((j + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((j : ℂ) + 2) ≠ 0 := by
    have : ((j : ℝ) + 2) ≠ 0 := by positivity
    exact_mod_cast this
  simp only [emC]
  set u : ℂ := (-1) ^ j with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← pow_add, ← two_mul, pow_mul]; norm_num
  have hpj : ((-1 : ℂ) ^ (j + 1)) = u * (-1) := by rw [hu, pow_succ]
  rw [hpj]
  set P := poch s (j + 1)
  set X := ((N : ℝ) : ℂ) ^ (-s - ((j + 1 : ℕ) : ℂ))
  set T := emTail s N (j + 1 + 1)
  set b := (bernoulli (j + 1 + 1) : ℂ)
  have hc : ((j + 1 : ℕ) : ℂ) + 1 = (j : ℂ) + 2 := by push_cast; ring
  rw [hc]
  field_simp
  linear_combination (b * P * X) * hu2
