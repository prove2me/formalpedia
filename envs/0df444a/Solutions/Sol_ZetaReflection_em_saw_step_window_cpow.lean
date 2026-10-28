-- Prove2me | solution 1 for ZetaReflection.em_saw_step_window_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:47.295958+00:00
-- url     : https://prove2.me/submissions/27f8c56b-afe8-4bd7-a6b6-36356b5d4fac

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
import Theorems.Thm_ZetaReflection_em_saw_step_cpow
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









/-- On the half-open unit cell starting at an integer, the saw agrees with the raw Bernoulli
    function shifted to that cell. -/
lemma sawBernoulli_eq_on_Ico (k : ℕ) {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli k x = bernoulliFun k (x - m) := by
  have hfloor : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, by push_cast; linarith [hx.2]⟩
  have hfract : Int.fract x = x - m := by
    rw [Int.fract, hfloor]
  rw [sawBernoulli, hfract]



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

namespace ZetaReflection

/-! ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/









/-! ## G. The saw-order-raising IBP step over a unit cell.

    The antiderivative tower: `sawBernoulli (k+1) / (k+1)` has derivative `sawBernoulli k` on the
    OPEN cell `(m, m+1)` (from `antideriv_bernoulliFun`, since `Int.fract` has derivative `1` off
    ℤ and `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k`).  IBP with this antiderivative
    turns `∫ sawBernoulli k · fk` into a boundary term plus `∫ sawBernoulli (k+1) · fk'`, exactly
    one order higher.  The endpoint saw values are `bernoulliFun (k+1) 0` and `bernoulliFun (k+1) 1`
    (the cell is `[m, m+1]`), which for `k+1 ≠ 1` are EQUAL by `bernoulliFun_endpoints_eq_of_ne_one`
    — the mechanism that makes the interior Bernoulli boundary terms telescope to zero. -/













/-- ℂ-valued telescoping sum of first differences. -/
private lemma sum_telescope_diff_cpow (g : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ j ∈ Finset.Ico M N, (g ((j : ℝ) + 1) - g (j : ℝ))) = g (N : ℝ) - g (M : ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih => rw [Finset.sum_Ico_succ_top hp, ih]; push_cast; ring

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



/-! ## H'. The SHIFTED-BASE tail engine `(w + x)^{-a}` (the Binet / Γℝ substrate).

    The base-1 engine `em_tail_integral_bound` bounds saw-weighted `x^{-s-k}` tails.  The Binet
    remainder `μ_K(w)` (Stirling series for `ψ`) is, up to the finite Bernoulli peel, an
    Euler–Maclaurin tail of the trigamma power series `Σ (w+n)^{-2-k}` — a SHIFTED-BASE `(w+x)^{-a}`
    tail.  This subsection generalizes the engine to that base.  Crucially the exponent is kept REAL
    (`a : ℝ`, `a > 1`) — which is exactly the form the trigamma tail needs (`a = 2 + k ∈ ℕ`) — so
    the norm is `‖(w+x)^{-a}‖ = ‖w+x‖^{-a}` (`Complex.norm_cpow_real`, no `exp(arg·im)` factor), and
    the honest `N`-decay is driven by the base lower bound `‖w+x‖ ≥ Re(w+x) = Re w + x ≥ Re w + N`. -/





/-! ## I. The K = 3 instance and THE NUMBER (the go/no-go for full reflection).

    The order-3 tail remainder integrand is `sawBernoulli 3 x · (c₃(s) · x^{-s-3})` where
    `c₃(s) = -s(s+1)(s+2)` is the coefficient of `x^{-s-3}` in `d³/dx³(x^{-s})`.  `em_tail_integral_bound`
    bounds this integral for ANY complex `c`; here we record it with the honest falling-factorial
    coefficient and the proven saw-3 sup bound `1/12`, then evaluate the numeric envelope at the G2
    pilot point `s = 1/2 + 14i` and certify a tail cut making it `< 10⁻³` (the K = 1 envelope
    `‖s‖/(2·Re s) ≈ 14` did NOT — see EMZetaComplex.em_zeta_strip_enclosure). -/









/-! ## J. The order-2 windowed EM identity for the ζ integrand (complex).

    We raise the K=1 windowed complex EM identity (`euler_maclaurin_one_window_cpow` applied to
    `f x = (x:ℂ)^(-s)`) to order 2 using `em_saw_step_window` (real coefficients, applied to the
    real and imaginary parts — but here directly to the ℂ integrand via linearity of the identity
    over the real saw).  The order-2 remainder integrand carries the coefficient `c₂(s) = s(s+1)`.

    We give the complex σ-direction derivatives to order 2 (the inputs `em_saw_step_window` needs),
    then the windowed order-2 identity.  This is the reusable step; iterating once more gives order 3,
    and the `[N,∞)` limit (handoff) yields the ζ representation. -/



/-! ### ℂ-valued saw-order-raising over a window (for the ζ integrand).

    The ℂ lift of `em_saw_step` and `em_saw_step_window`.  The saw factor `sawBernoulli k x` stays
    REAL (cast to ℂ); `fk, fk1` are ℂ-valued.  Proof structure is identical to the real versions
    with `linear_combination` in place of `linarith` for the final ℂ arithmetic. -/





/-! ## K. The order-2 tail identity for the ζ integrand, and its `[N, ∞)` form.

    Raising the K=1 saw remainder integrand `saw₁·(−s x^{−s−1})` to order 2 on the tail `[N, ∞)`.
    Over a finite window `[N, M]` this is `em_saw_step_window_cpow` (k=1); taking `M → ∞` (the K=1
    endpoint value `−s·M^{−s−1} → 0`, and both integrals converge for `Re s > 0`) yields
        ∫_N^∞ saw₁·(−s x^{−s−1})
          = B₂(0)·(s·N^{−s−1})/2  −  (∫_N^∞ saw₂·(s(s+1) x^{−s−2}))/2,
    with `B₂(0) = bernoulli 2 = 1/6`.  This is the order-2 tail EM step in closed form. -/













/-! ## L. The assembled order-3 tail identity and the ζ enclosure (checkBand consumer form). -/













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



/-! ## H'. The SHIFTED-BASE tail engine `(w + x)^{-a}` (the Binet / Γℝ substrate).

    The base-1 engine `em_tail_integral_bound` bounds saw-weighted `x^{-s-k}` tails.  The Binet
    remainder `μ_K(w)` (Stirling series for `ψ`) is, up to the finite Bernoulli peel, an
    Euler–Maclaurin tail of the trigamma power series `Σ (w+n)^{-2-k}` — a SHIFTED-BASE `(w+x)^{-a}`
    tail.  This subsection generalizes the engine to that base.  Crucially the exponent is kept REAL
    (`a : ℝ`, `a > 1`) — which is exactly the form the trigamma tail needs (`a = 2 + k ∈ ℕ`) — so
    the norm is `‖(w+x)^{-a}‖ = ‖w+x‖^{-a}` (`Complex.norm_cpow_real`, no `exp(arg·im)` factor), and
    the honest `N`-decay is driven by the base lower bound `‖w+x‖ ≥ Re(w+x) = Re w + x ≥ Re w + N`. -/





/-! ## I. The K = 3 instance and THE NUMBER (the go/no-go for full reflection).

    The order-3 tail remainder integrand is `sawBernoulli 3 x · (c₃(s) · x^{-s-3})` where
    `c₃(s) = -s(s+1)(s+2)` is the coefficient of `x^{-s-3}` in `d³/dx³(x^{-s})`.  `em_tail_integral_bound`
    bounds this integral for ANY complex `c`; here we record it with the honest falling-factorial
    coefficient and the proven saw-3 sup bound `1/12`, then evaluate the numeric envelope at the G2
    pilot point `s = 1/2 + 14i` and certify a tail cut making it `< 10⁻³` (the K = 1 envelope
    `‖s‖/(2·Re s) ≈ 14` did NOT — see EMZetaComplex.em_zeta_strip_enclosure). -/









/-! ## J. The order-2 windowed EM identity for the ζ integrand (complex).

    We raise the K=1 windowed complex EM identity (`euler_maclaurin_one_window_cpow` applied to
    `f x = (x:ℂ)^(-s)`) to order 2 using `em_saw_step_window` (real coefficients, applied to the
    real and imaginary parts — but here directly to the ℂ integrand via linearity of the identity
    over the real saw).  The order-2 remainder integrand carries the coefficient `c₂(s) = s(s+1)`.

    We give the complex σ-direction derivatives to order 2 (the inputs `em_saw_step_window` needs),
    then the windowed order-2 identity.  This is the reusable step; iterating once more gives order 3,
    and the `[N,∞)` limit (handoff) yields the ζ representation. -/



/-! ### ℂ-valued saw-order-raising over a window (for the ζ integrand).

    The ℂ lift of `em_saw_step` and `em_saw_step_window`.  The saw factor `sawBernoulli k x` stays
    REAL (cast to ℂ); `fk, fk1` are ℂ-valued.  Proof structure is identical to the real versions
    with `linear_combination` in place of `linarith` for the final ℂ arithmetic. -/




theorem solution {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hMN : M ≤ N) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt fk (fk1 x) x)
    (hi : ∀ j ∈ Finset.Ico M N, IntervalIntegrable fk1 volume (j : ℝ) (j + 1)) :
    (∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1)
        - (∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hk1ne : k + 1 ≠ 1 := by omega
  have hendeq : (bernoulliFun (k + 1) 1 : ℂ) = (bernoulliFun (k + 1) 0 : ℂ) := by
    exact_mod_cast bernoulliFun_endpoints_eq_of_ne_one hk1ne
  have hcell : ∀ j ∈ Finset.Ico M N, ∀ x ∈ Icc (j : ℝ) (j + 1), HasDerivAt fk (fk1 x) x := by
    intro j hj x hx
    rw [Finset.mem_Ico] at hj
    refine hd x ⟨le_trans (by exact_mod_cast hj.1) hx.1, ?_⟩
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj.2
    linarith [hx.2]
  have hstep : ∀ j ∈ Finset.Ico M N,
      (∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
        = ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j) / (k + 1)
          - (∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    intro j hj
    have hcast : (((j : ℤ)) : ℝ) = (j : ℝ) := by push_cast; ring
    have := em_saw_step_cpow k (j : ℤ) fk fk1
      (by intro x hx; rw [hcast] at hx; exact hcell j hj x hx)
      (by rw [hcast]; exact hi j hj)
    simpa [hcast] using this
  have hsum := Finset.sum_congr rfl hstep
  -- Integrability per cell (ℂ).
  have hint_k : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hfkcont : ContinuousOn fk (Icc (j : ℝ) (j + 1)) :=
      fun x hx => (hcell j hj x hx).continuousAt.continuousWithinAt
    have hcont : IntervalIntegrable (fun x => (bernoulliFun k (x - j) : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hfkcont
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico k hxIco]; norm_num
  have htel_k : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli k x : ℂ) * fk x) (μ := volume) hMN hint
    simpa using this
  have hint_k1 : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => (bernoulliFun (k + 1) (x - j) : ℂ) * fk1 x) volume
        (j : ℝ) (j + 1) := (hi j hj).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco]; norm_num
  have htel_k1 : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k1 j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) (μ := volume) hMN hint
    simpa using this
  -- Boundary telescoping (ℂ).
  have hbdry : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j)) / (k + 1)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1) := by
    congr 1
    rw [hendeq]
    have hcongr : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 0 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j))
        = (∑ j ∈ Finset.Ico M N,
            (bernoulliFun (k + 1) 0 : ℂ) * (fk ((j : ℝ) + 1) - fk (j : ℝ))) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hcongr, ← Finset.mul_sum, sum_telescope_diff_cpow fk hMN]
  rw [Finset.sum_sub_distrib] at hsum
  rw [← Finset.sum_div, ← Finset.sum_div, htel_k1, htel_k, hbdry] at hsum
  exact hsum
