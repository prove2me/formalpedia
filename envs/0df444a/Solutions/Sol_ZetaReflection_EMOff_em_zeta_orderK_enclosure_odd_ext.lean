-- Prove2me | solution 1 for ZetaReflection.EMOff.em_zeta_orderK_enclosure_odd_ext
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:13:32.110269+00:00
-- url     : https://prove2.me/submissions/9d45c135-2433-4eab-9e83-0c1ef7114474

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
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
import Theorems.Thm_ZetaReflection_EMOff_em_zeta_order_ext
import Theorems.Thm_ZetaReflection_em_tail_integral_bound
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
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


/-  EMZetaOfflineCore.lean -- lane offline (ANDURIL Arb discharge, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    brick B6 / K2): the general-order Euler-Maclaurin representation of ζ OFF the critical line.

    `EMZetaHigh.em_zeta_order` proves the order-`m` identity
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!
    on `Re s > 0` only (it is transported from the K = 1 continuation `em_zeta_strip`).  The tail
    integral converges on the larger half-plane `Re s > 1 - m`, so the identity extends there by the
    identity theorem.  This file proves that extension and the resulting remainder bounds for
    every real part `σ > 1 - 2K` (even saw) and `σ > -2K` (odd saw):

      O1.  `emTail_eq_mellin`        -- the tail is `emC s m · mellin (sawCut m N) (1 - s - m)`;
      O2.  `emTail_differentiableAt` -- hence complex-differentiable on `Re s > 1 - m`
                                        (`mellin_differentiableAt_of_isBigO_rpow`);
      O3.  `emFiniteM_differentiableAt` -- the finite part is differentiable off `s = 1`;
      O4.  `em_zeta_order_ext`       -- THE CONTINUATION: the order-`m` identity on `Re s > 1 - m`,
                                        `s ≠ 1` (identity theorem on the convex strip
                                        `1 - m < Re s < 1`, anchored at `s = 1/2`);
      O5.  `em_zeta_orderK_enclosure_ext`, `em_zeta_orderK_enclosure_odd_ext` -- the general-K
                                        remainder bounds of `EMZetaHigh` for `σ > 1 - 2K`,
                                        resp. `σ > -2K` (so `σ = -1` is covered from `K = 1` on).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin + analytic
    continuation); it says nothing about the Riemann Hypothesis.
-/


open MeasureTheory Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMOff

open EMHigh

/-! ## O1. The tail as a Mellin transform. -/





/-! ## O2. Differentiability of the tail on `Re s > 1 - m`. -/













/-! ## O3. Differentiability of the finite part off `s = 1`. -/



/-! ## O4. THE CONTINUATION of the order-`m` identity to `Re s > 1 - m`. -/



/-! ## O5. The general-K remainder bounds off the critical line. -/

/-- The tail bound for every `s` with `Re s + m > 1` (`EMHigh.emTail_norm_le` assumed `Re s > 0`). -/
theorem emTail_norm_le_ext (m : ℕ) {s : ℂ} (h : 1 < s.re + m) {N : ℕ} (hN : 1 ≤ N)
    {B : ℝ} (hB0 : 0 ≤ B) (hsaw : ∀ x : ℝ, |sawBernoulli m x| ≤ B) :
    ‖emTail s N m‖ ≤ B * ‖poch s m‖ * (N : ℝ) ^ (-(s.re + m - 1)) / (s.re + m - 1) := by
  have h' := em_tail_integral_bound (k := m) (s := s) (c := emC s m) (B := B) (N := N) hN h hB0 hsaw
  rw [norm_emC] at h'
  exact h'





end EMOff

end ZetaReflection


/-  EMZetaOfflineCore.lean -- lane offline (ANDURIL Arb discharge, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    brick B6 / K2): the general-order Euler-Maclaurin representation of ζ OFF the critical line.

    `EMZetaHigh.em_zeta_order` proves the order-`m` identity
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!
    on `Re s > 0` only (it is transported from the K = 1 continuation `em_zeta_strip`).  The tail
    integral converges on the larger half-plane `Re s > 1 - m`, so the identity extends there by the
    identity theorem.  This file proves that extension and the resulting remainder bounds for
    every real part `σ > 1 - 2K` (even saw) and `σ > -2K` (odd saw):

      O1.  `emTail_eq_mellin`        -- the tail is `emC s m · mellin (sawCut m N) (1 - s - m)`;
      O2.  `emTail_differentiableAt` -- hence complex-differentiable on `Re s > 1 - m`
                                        (`mellin_differentiableAt_of_isBigO_rpow`);
      O3.  `emFiniteM_differentiableAt` -- the finite part is differentiable off `s = 1`;
      O4.  `em_zeta_order_ext`       -- THE CONTINUATION: the order-`m` identity on `Re s > 1 - m`,
                                        `s ≠ 1` (identity theorem on the convex strip
                                        `1 - m < Re s < 1`, anchored at `s = 1/2`);
      O5.  `em_zeta_orderK_enclosure_ext`, `em_zeta_orderK_enclosure_odd_ext` -- the general-K
                                        remainder bounds of `EMZetaHigh` for `σ > 1 - 2K`,
                                        resp. `σ > -2K` (so `σ = -1` is covered from `K = 1` on).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin + analytic
    continuation); it says nothing about the Riemann Hypothesis.
-/


open MeasureTheory Set Filter Topology Complex
open scoped Real Nat

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

section
namespace ZetaReflection.EMOff
end ZetaReflection.EMOff
open ZetaReflection.EMOff

open EMHigh

/-! ## O1. The tail as a Mellin transform. -/





/-! ## O2. Differentiability of the tail on `Re s > 1 - m`. -/













/-! ## O3. Differentiability of the finite part off `s = 1`. -/



/-! ## O4. THE CONTINUATION of the order-`m` identity to `Re s > 1 - m`. -/



/-! ## O5. The general-K remainder bounds off the critical line. -/






theorem solution (K : ℕ) (hK : 1 ≤ K) {s : ℂ}
    (hs : -((2 * K : ℕ) : ℝ) < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 * K + 1 := by omega
  have hs' : 1 - ((2 * K + 1 : ℕ) : ℝ) < s.re := by push_cast at hs ⊢; linarith
  have hid := em_zeta_order_ext (2 * K + 1) hm hs' hs1 hN
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
  have hbd := emTail_norm_le_ext (2 * K + 1) (s := s) (by push_cast at hs ⊢; linarith) hN hB0
    (abs_sawBernoulli_odd_le K (by omega))
  calc ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ)
      ≤ (2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
          / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / ((2 * K + 1)! : ℝ) :=
        div_le_div_of_nonneg_right hbd hF.le
    _ = _ := by field_simp
