-- Prove2me | solution 1 for ZetaReflection.EMHigh.em_zeta_order
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:07:44.79301+00:00
-- url     : https://prove2.me/submissions/41b02b98-ad45-4b97-ab86-3eadaf4d990e

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
import Theorems.Thm_ZetaReflection_EMHigh_emTail_unroll_step
import Theorems.Thm_ZetaReflection_em_cpow_partial
import Theorems.Thm_ZetaReflection_em_cpow_remainder_integrableOn_strip
import Theorems.Thm_ZetaReflection_em_zeta_strip
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









lemma emC_one (s : ℂ) : emC s 1 = -s := by
  simp [emC, poch_succ, poch]



/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/



/-- **Unrolled tail.**  For every `j`, the saw-1 tail equals the explicit Bernoulli corrections
    `Σ_{i<j} B_{i+2} (s)_{i+1} N^{-s-(i+1)} / (i+2)!` plus the order-`(j+1)` remainder
    `(-1)^j emTail s N (j+1) / (j+1)!`. -/
theorem emTail_unroll {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    emTail s N 1
      = (∑ i ∈ Finset.range j, (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ)
            * ((N : ℝ) : ℂ) ^ (-s - ((i + 1 : ℕ) : ℂ)))
        + (-1) ^ j * emTail s N (j + 1) / ((j + 1)! : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, Finset.sum_range_succ, emTail_unroll_step hs hN j]
    ring

/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/













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




theorem solution (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    riemannZeta s = emFiniteM m s N + (-1) ^ (m - 1) * emTail s N m / (m ! : ℂ) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hK1 := em_zeta_strip hs hs1
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- split ∫_1^∞ = ∫_1^N + ∫_N^∞
  have hI1_Ioi : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      (Ioi 1) := em_cpow_remainder_integrableOn_strip hs
  have hsplit : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    have hIcc : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        (Ioc 1 N) := hI1_Ioi.mono_set Ioc_subset_Ioi_self
    have hIoiN : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        (Ioi N) := hI1_Ioi.mono_set (Ioi_subset_Ioi h1N)
    have hunion : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        = (∫ x in Ioc (1 : ℝ) N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
          + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIcc hIoiN,
        Set.Ioc_union_Ioi_eq_Ioi h1N]
    rw [hunion, ← intervalIntegral.integral_of_le h1N]
  -- the tail is emTail s N 1
  have htail : (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = emTail s N 1 := by
    simp only [emTail, emC_one, Nat.cast_one]
  -- the Dirichlet rewrite of the [1,N] saw integral
  have hpart := em_cpow_partial hs0 (N := N) hN
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
      = (((N : ℝ) : ℂ) ^ (-s + 1) - ((1 : ℝ) : ℂ) ^ (-s + 1)) / (-s + 1) := by
    apply integral_cpow
    right
    refine ⟨?_, ?_⟩
    · intro h; apply hs1; linear_combination -h
    · rw [Set.uIcc_of_le h1N]; intro h; have := h.1; linarith
  have hunroll := emTail_unroll hs hN (m - 1)
  rw [show m - 1 + 1 = m by omega] at hunroll
  rw [hK1, hsplit, htail, hunroll]
  -- normalize casts and powers
  have hNc : ((N : ℝ) : ℂ) = (N : ℂ) := Complex.ofReal_natCast N
  have hone : ((1 : ℝ) : ℂ) = 1 := Complex.ofReal_one
  rw [hint, hNc, hone] at hpart
  simp only [Complex.one_cpow] at hpart
  simp only [hNc, emFiniteM]
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hden : (-s + 1) ≠ 0 := by
    rw [show (-s + 1 : ℂ) = -(s - 1) by ring]; exact neg_ne_zero.mpr hsm1
  have hpow : (N : ℂ) ^ (-s + 1) = (N : ℂ) ^ (1 - s) := by rw [show (-s + 1 : ℂ) = 1 - s by ring]
  rw [hpow] at hpart
  set Isaw : ℂ := ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))
    with hIsaw
  set S : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) with hS
  have hIsaw_eq : Isaw = S - ((N : ℂ) ^ (1 - s) - 1) / (-s + 1) + ((N : ℂ) ^ (-s) - 1) / 2 := by
    linear_combination -hpart
  rw [hIsaw_eq]
  field_simp
  ring
