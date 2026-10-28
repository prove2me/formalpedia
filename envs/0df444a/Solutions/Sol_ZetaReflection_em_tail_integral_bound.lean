-- Prove2me | solution 1 for ZetaReflection.em_tail_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:45:23.83718+00:00
-- url     : https://prove2.me/submissions/206f168f-e04d-4430-8962-ffe9eb4fd4ec

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
/-  EMZeta.lean -- A2 Theorem 1: the Euler-Maclaurin representation of ζ with explicit
    remainder.

    Euler-Maclaurin summation is ABSENT from Mathlib (confirmed: `find Mathlib -iname
    '*maclaurin*'` is empty; `Mathlib/Analysis/SumIntegralComparisons.lean` has only crude
    monotone sum/integral bounds).  This file builds it bottom-up and is upstreamable.

    Architecture (proven bottom-up; only fully-proven lemmas live here, WIP in EMZetaWip.lean):

      A.  Periodized ("saw") Bernoulli  `sawBernoulli k x := bernoulliFun k (Int.fract x)`.
          Reuses `Mathlib.NumberTheory.ZetaValues.bernoulliFun` and its derivative/integral
          API (`hasDerivAt_bernoulliFun`, `integral_bernoulliFun`, `contDiff_bernoulliFun`).

      B.  One-step Euler-Maclaurin over `[m, m+1]` for a C^1 function f:
              ∫ f = (f m + f (m+1))/2 - ∫ B̃₁(x) f'(x) dx
          via integration by parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`)
          with the saw-1 antiderivative.  This is `em_unit_step`.

      C.  Summed over `m = 0 .. N-1`: the classical first-order Euler-Maclaurin formula
              ∑_{n=1}^{N} f n = ∫_0^N f + (f N - f 0)/2 + ∫_0^N B̃₁(x) f'(x) dx
          (`euler_maclaurin_one`).  Telescoping of the integral (`intervalIntegral.sum_integral_
          adjacent_intervals`) + telescoping of the trapezoid endpoints.

      D.  Specialisation to `f x = x^{-s}` on `[1, N]` (real `s`) and the tail limit `N → ∞`
          giving the K=1 Euler-Maclaurin representation of `ζ` for real `s > 1`
          (`em_zeta_real_K1`), matching the Mathlib fractional-part representation route
          used in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.

    NOT YET in this file (see EMZetaWip.lean, never imported by a guard, never `sorry` here):
      - the general order-K induction (periodized `bernoulliFun k` for k ≥ 2);
      - the complex interval-σ form valid `Re s > 1 - 2K` by analytic continuation
        (`AnalyticOnNhd.eqOn`);
      - the explicit remainder BOUND `|R_K| ≤ (|B_{2K}|/(2K)!) ∫ |f^{(2K)}|`.

    conjecture1_proved = False.  This is NOT a proof of RH; it is a classical analysis lemma.
-/







open MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace ZetaReflection

/-! ## A. The periodized ("saw") Bernoulli functions -/





/-- The saw is measurable: `bernoulliFun k` is continuous and `Int.fract` is measurable. -/
lemma sawBernoulli_measurable (k : ℕ) : Measurable (sawBernoulli k) :=
  (contDiff_bernoulliFun (k := k)).continuous.measurable.comp measurable_fract







/-! ## B. One-step Euler-Maclaurin over a unit cell

    For a `C¹` function `f` on `[m, m+1]` (real, integer `m`), integration by parts with the
    order-1 antiderivative `w x = x - m - 1/2` of the constant `1` (equal to `sawBernoulli 1`
    on the cell) yields the trapezoidal Euler-Maclaurin step
        ∫_m^{m+1} f = (f m + f(m+1))/2 − ∫_m^{m+1} (sawBernoulli 1 x) · f'(x) dx.
-/



/-! ## C. Summed first-order Euler-Maclaurin over `[0, N]`

    Summing `em_unit_step` over the cells `[0,1], [1,2], …, [N-1,N]` and telescoping the two
    integrals with `intervalIntegral.sum_integral_adjacent_intervals` gives the classical
    first-order Euler-Maclaurin formula (sum indexed `1..N`, integral over `[0,N]`)
        ∑_{n=1}^{N} f n = ∫_0^N f + (f N − f 0)/2 + ∫_0^N (sawBernoulli 1 x)·f'(x) dx.
    (Equivalently `∑_{n=0}^{N} f n = ∫_0^N f + (f 0 + f N)/2 + remainder`, the textbook form.)
-/







/-! ## D. Zeta base case: first-order Euler-Maclaurin for `f x = x^{-s}` on `[1, N]`

    The reusable finite-`N` statement.  Specialising the general `[M, N]` machinery below to
    `M = 1`, `f x = x^{-s}` with derivative `f' x = -s · x^{-s-1}` (valid for `x ≠ 0`, hence on
    all of `[1, N]`), we get the classical finite Euler-Maclaurin representation of the partial
    zeta sum.  Taking `N → ∞` (real `s > 1`) matches the fractional-part representation in
    `Mathlib.NumberTheory.Harmonic.ZetaAsymp` (`zeta_limit_aux1`, `termTSum`).
-/









end ZetaReflection


/-  EMZetaTail.lean -- A2 Theorem 1, TAIL track: the order-K Euler-Maclaurin tail engine.

    The blocker of PROGRAM ANDÚRIL's reflection track.  Builds on `EMZeta.lean` /
    `EMZetaComplex.lean` (the K=1 chain).  The K=1 remainder envelope `‖s‖/(2·Re s)` proven in
    `EMZetaComplex.em_zeta_strip_enclosure` is sign-LOOSE (≈14 at s=1/2+14i), so the G2 reflected
    band could not be made sign-tight from it.  This file raises the Euler-Maclaurin order and cuts
    the sum at a finite `N`, producing a remainder that DECAYS like `N^{-Re s - K + 1}`, small enough
    to make `gLine` boxes sign-tight.

    Architecture (bottom-up), ALL kernel-clean (AxiomGuardEMTail):

      F.  Order-2/3 periodized "saw" Bernoulli sup bounds: `|sawBernoulli 2| ≤ 1/6`,
          `|sawBernoulli 3| ≤ 1/12` (via `B₃ = y(1−y)(1/2−y)`), and `bernoulliFun_three` closed form.
      G.  `em_saw_step` — the one IBP step raising the saw order by one over a unit cell (the proven
          form of `EMZetaWip.em_saw_step_wip`), via the continuous polynomial surrogate
          `B_{k+1}(x−m)/(k+1)`.  Endpoint saw values `B_{k+1}(0)`, `B_{k+1}(1)` (equal for `k+1≠1`).
      G'. `em_saw_step_window` — sum `em_saw_step` over `[M,N]`; interior boundary terms telescope
          (`bernoulliFun_endpoints_eq_of_ne_one`), leaving only `B_{k+1}(0)(fk N − fk M)/(k+1)`.
      H.  `em_tail_integral_bound` — the reusable engine: `‖∫_N^∞ saw_k · c·x^{−s−k}‖`
          ≤ `B·‖c‖·N^{−(Re s+k−1)}/(Re s+k−1)`, the `N`-decay that makes gLine boxes sign-tight.
      I.  `em_tail3_bound` (order-3, `B = 1/12`) and `em_tail3_number` — THE NUMBER: at the G2 pilot
          `s = 1/2 + 14i`, `N = 200`, the order-3 remainder is `≤ 10⁻³` (kernel-decided).  Clears the
          go/no-go the K=1 envelope `‖s‖/(2·Re s) ≈ 14` failed.

    REMAINING for the full ζ-order-K identity (handoff): tie `em_saw_step_window` to `riemannZeta` by
    raising the K=1 remainder `∫_1^∞ saw₁·(−s x^{−s−1})` (from `EMZetaComplex.em_zeta_strip`) to
    order 3 over `[N,∞)` — apply `em_saw_step_window` on `[N,M]` (complex cpow orders 2,3, derivative
    coefficients `s(s+1)…`), then `M → ∞` (boundary terms → 0; integral → `∫_N^∞`), reusing the
    `intervalIntegral_tendsto_integral_Ioi` limit pattern from `em_zeta_cpow`.  The remainder BOUND at
    the endpoint is already `em_tail3_bound`; only the identity plumbing remains.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin tail bound),
    NOT a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

/-! ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/









/-! ## G. The saw-order-raising IBP step over a unit cell.

    The antiderivative tower: `sawBernoulli (k+1) / (k+1)` has derivative `sawBernoulli k` on the
    OPEN cell `(m, m+1)` (from `antideriv_bernoulliFun`, since `Int.fract` has derivative `1` off
    ℤ and `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k`).  IBP with this antiderivative
    turns `∫ sawBernoulli k · fk` into a boundary term plus `∫ sawBernoulli (k+1) · fk'`, exactly
    one order higher.  The endpoint saw values are `bernoulliFun (k+1) 0` and `bernoulliFun (k+1) 1`
    (the cell is `[m, m+1]`), which for `k+1 ≠ 1` are EQUAL by `bernoulliFun_endpoints_eq_of_ne_one`
    — the mechanism that makes the interior Bernoulli boundary terms telescope to zero. -/















/-! ## G'. Summed saw-order-raising over an integer window `[M, N]`.

    Summing `em_saw_step` over the cells `[M,M+1], …, [N-1,N]` and telescoping via
    `sum_integral_adjacent_intervals_Ico`, the interior boundary terms cancel (for `k+1 ≠ 1` the
    saw endpoint values `B_{k+1}(0) = B_{k+1}(1)` agree, so adjacent cells contribute
    `+B_{k+1}(0)·f(j)` and `−B_{k+1}(0)·f(j)`), leaving only the two outer endpoints:
        ∫_M^N saw_k · fk
          = B_{k+1}(0)·(fk N − fk M)/(k+1)  −  (∫_M^N saw_{k+1} · fk1)/(k+1).
    (Here `k ≥ 1` so `k + 1 ≠ 1`, which is what makes the telescoping clean.) -/



/-! ## H. The order-K tail remainder integrals and their explicit `N`-decaying bounds.

    The consumer needs a remainder over the TAIL `[N, ∞)` whose norm decays in `N`.  We work with
    the complex integrand `sawBernoulli k x · (c · (x:ℂ)^(-s-k))` where `c` is the falling-factorial
    coefficient `(-1)^k s(s+1)…(s+k-1)` (the k-th derivative coefficient of `x^{-s}`).  The norm
    bound is the clean product form
        ‖∫_N^∞ saw_k · c·x^{-s-k}‖ ≤ Bsup_k · ‖c‖ · N^{-Re s - k + 1} / (Re s + k - 1),
    from `‖saw_k‖ ≤ Bsup_k`, `‖x^{-s-k}‖ = x^{-Re s - k}`, and `∫_N^∞ x^{-Re s -k} = N^{-Re s -k+1}/(Re s+k-1)`. -/


theorem solution {k : ℕ} {s c : ℂ} {B : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hexp : 1 < s.re + k) (hB : 0 ≤ B)
    (hsawB : ∀ x : ℝ, |sawBernoulli k x| ≤ B) :
    ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hσk1 : 0 < s.re + k - 1 := by linarith
  -- exponent for the norm: -(Re s + k) < -1.
  have hexplt : -(s.re + (k : ℝ)) < -1 := by
    have : (1 : ℝ) < s.re + k := hexp
    linarith
  -- integrand norm domination: ‖·‖ ≤ (B·‖c‖) · x^{-(Re s + k)} on (N,∞).
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖c‖) * x ^ (-(s.re + (k : ℝ)))) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos).const_mul _
  have hInt : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k)))
      (Ioi (N : ℝ)) := by
    refine Integrable.mono' hdom ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable k)).mul
        (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
      have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        congr 1
        rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
        ring
      have hrpownn : (0 : ℝ) ≤ x ^ (-(s.re + (k : ℝ))) := Real.rpow_nonneg hxpos.le _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
      calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
          ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
            gcongr; exact hsawB x
        _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
  -- ‖∫‖ ≤ ∫‖·‖ ≤ ∫ dom = (B‖c‖)·N^{-(σ+k-1)}/(σ+k-1).
  calc ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ ∫ x in Ioi (N : ℝ), ‖(sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (N : ℝ), (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by
        apply setIntegral_mono_on hInt.norm hdom measurableSet_Ioi
        intro x hx
        have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
        have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
          congr 1
          rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
        calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
            ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
              gcongr; exact hsawB x
          _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
    _ = B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos]
        have hexp1 : -(s.re + (k : ℝ)) + 1 = -(s.re + k - 1) := by ring
        rw [hexp1]
        have hne : s.re + (k : ℝ) - 1 ≠ 0 := ne_of_gt hσk1
        field_simp
