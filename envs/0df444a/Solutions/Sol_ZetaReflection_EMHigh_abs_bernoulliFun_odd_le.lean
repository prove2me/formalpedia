-- Prove2me | solution 1 for ZetaReflection.EMHigh.abs_bernoulliFun_odd_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:30.396779+00:00
-- url     : https://prove2.me/submissions/01f4c8aa-e3c6-491b-84d1-ef570949b586

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
import Theorems.Thm_ZetaReflection_EMHigh_hasSum_one_div_pow_le

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




theorem solution (K : ℕ) (hK : K ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * K + 1) x|
      ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
  have hx' := hasSum_one_div_nat_pow_mul_sin hK hx
  have hBx : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * K + 1))).eval x
      = bernoulliFun (2 * K + 1) x := rfl
  rw [hBx] at hx'
  set C : ℝ := (-1 : ℝ) ^ (K + 1) * (2 * π) ^ (2 * K + 1) / 2 / (2 * K + 1)! with hCdef
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * K + 1)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hS := hsum.hasSum
  set S := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * K + 1) with hSdef
  have hle1 : C * bernoulliFun (2 * K + 1) x ≤ S := by
    refine hasSum_le (fun n => ?_) hx' hS
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K + 1) := by positivity
    calc 1 / (n : ℝ) ^ (2 * K + 1) * Real.sin (2 * π * n * x)
        ≤ 1 / (n : ℝ) ^ (2 * K + 1) * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) hnn
      _ = 1 / (n : ℝ) ^ (2 * K + 1) := by ring
  have hle2 : -(C * bernoulliFun (2 * K + 1) x) ≤ S := by
    refine hasSum_le (fun n => ?_) hx'.neg hS
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K + 1) := by positivity
    have := Real.neg_one_le_sin (2 * π * n * x)
    show -(1 / (n : ℝ) ^ (2 * K + 1) * Real.sin (2 * π * n * x)) ≤ 1 / (n : ℝ) ^ (2 * K + 1)
    nlinarith
  have habs : |C * bernoulliFun (2 * K + 1) x| ≤ S := abs_le.mpr ⟨by linarith, hle1⟩
  have hSle := hasSum_one_div_pow_le (p := 2 * K + 1) (by omega) hS
  rw [show 2 * K + 1 - 2 = 2 * K - 1 by omega] at hSle
  have hCabs : |C| = (2 * π) ^ (2 * K + 1) / 2 / (2 * K + 1)! := by
    rw [hCdef, abs_div, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (2 * K + 1)), abs_two,
      abs_of_pos (by exact_mod_cast Nat.factorial_pos _ : (0 : ℝ) < ((2 * K + 1)! : ℝ))]
  have hCpos : 0 < |C| := by rw [hCabs]; positivity
  rw [abs_mul] at habs
  have hB : |bernoulliFun (2 * K + 1) x| ≤ S / |C| := by
    rw [le_div_iff₀ hCpos, mul_comm]; exact habs
  refine le_trans hB ?_
  rw [hCabs]
  have hF : (0 : ℝ) < ((2 * K + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi : (0 : ℝ) < (2 * π) ^ (2 * K + 1) := by positivity
  rw [div_div, div_div_eq_mul_div]
  calc S * (2 * ((2 * K + 1)! : ℝ)) / (2 * π) ^ (2 * K + 1)
      ≤ (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) * (2 * ((2 * K + 1)! : ℝ)) / (2 * π) ^ (2 * K + 1) := by
        gcongr
    _ = 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
        ring
