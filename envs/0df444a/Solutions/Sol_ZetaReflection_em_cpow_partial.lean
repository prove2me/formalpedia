-- Prove2me | solution 1 for ZetaReflection.em_cpow_partial
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:34.10987+00:00
-- url     : https://prove2.me/submissions/365d017a-8c78-40af-829b-0c5fe197c9c9

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Theorems.Thm_ZetaReflection_euler_maclaurin_one_window_cpow
/-  EMZetaComplex.lean -- A2 Theorem 1, E-track: the COMPLEX Euler-Maclaurin representation of ζ
    and its K=1 analytic continuation into the critical strip.

    Builds on `EMZeta.lean` (real-s EM chain, Parts A-D', kernel-clean).  This file is the
    complex lift and the analytic continuation:

      E1.  `em_unit_step_cpow`   -- one-step EM over [m,m+1] for a ℂ-valued C¹ function.
           `em_cpow_partial`      -- finite-N EM for `f x = (x:ℂ)^(-s)`, s : ℂ, on [1,N].
      E2.  `em_zeta_cpow`         -- N→∞ complex representation, valid Re s > 1, tied to riemannZeta.
      E3.  `em_zeta_strip`        -- K=1 analytic continuation to 0 < Re s (s ≠ 1) with explicit
                                     remainder bound (THE PRIZE — covers the critical strip).
      E4.  `em_zeta_strip_enclosure` -- evaluator-facing finite-sum + explicit-tail enclosure shape.

    Only fully-proven, sorry-free lemmas live here.  General-K (K ≥ 2) stays in EMZetaWip.lean.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin + identity
    theorem), NOT a proof of RH.
-/




open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace ZetaReflection

/-! ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/



/-! ## E1b. Summed complex EM over an integer window, and the partial-ζ identity.

    Lift of `euler_maclaurin_one_window` to ℂ-valued `f`.  The telescoping and per-cell
    integrability arguments are identical to the real proof; the trapezoid bookkeeping is over ℂ. -/





/-- The complex-power derivative on the positive reals (E1's `hasDerivAt_cpow_neg_wip`):
    `HasDerivAt (fun x:ℝ => (x:ℂ)^(-s)) (-s·(x:ℂ)^(-s-1)) x` for `x > 0` and `s ≠ 0`.
    Anchored on `hasDerivAt_ofReal_cpow_const`. -/
theorem hasDerivAt_cpow_neg {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hneg : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs
  have := hasDerivAt_ofReal_cpow_const (x := x) hx0 (r := -s) hneg
  simpa using this



/-! ## E2. The `N → ∞` complex representation for `Re s > 1`, tied to `riemannZeta`.

    Lift of `em_zeta_real` (Part D').  The three limits: partial sum → tsum (`summable_one_div_
    nat_cpow`), the two finite integrals → improper (`intervalIntegral_tendsto_integral_Ioi`),
    endpoint `N^{-s} → 0` (norm → 0).  Then `zeta_eq_tsum_one_div_nat_cpow` ties it to `ζ`. -/









/-! ## E3. K=1 analytic continuation into the critical strip (THE PRIZE).

    Define the EM closed form on `{Re s > 0}`:
        emZetaRemainder s := ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1})   -- converges for Re s > 0
        emZetaClosed s     := 1/(s−1) + 1/2 + emZetaRemainder s
    For `Re s > 1`, `∫_1^∞ x^{−s} = 1/(s−1)` and `1^{−s} = 1`, so `emZetaClosed s = riemannZeta s`
    (from `em_zeta_cpow_riemannZeta`).  Both `riemannZeta` and `emZetaClosed` are analytic on
    `{Re s > 0} \ {1}`, agree on the open set `{Re s > 1}` (which has accumulation points in the
    larger strip), so by the identity theorem they agree on all of `{Re s > 0} \ {1}`.  That is
    `em_zeta_strip`, which covers the whole critical strip. -/











/-! ### E3 helpers for the analytic continuation. -/











/-! ### The critical-strip half-plane, slit at `1`, is preconnected. -/





/-! ### E3 capstone: the identity theorem transfer. -/







/-! ## E4. Evaluator-facing enclosure (the A4 `checkBand` consumer shape).

    The A4 interval evaluator needs: an EXPLICIT finite part it can box with `DIntv` arithmetic,
    plus a RATIONAL error envelope on the (unevaluated) remainder.  `em_zeta_strip` already
    delivers exactly this at `K = 1`: the finite part is the elementary closed form
    `1/(s−1) + 1/2` (a reciprocal + a constant — directly boxable), and the remainder envelope is
    `‖s‖/(2·Re s)`.  We package it as a single norm enclosure, and give the `σ = 1/2 + it`
    critical-line specialization (the band the evaluator sweeps).

    Interface for A4 (`DIntvDef.DIntv.memR`): supplied dyadic-interval enclosures of `Re(1/(s−1))`,
    `Im(1/(s−1))`, the constant `1/2`, and the scalar envelope `‖s‖/(2·Re s)`, the evaluator boxes
    `Re(ζ s)` and `Im(ζ s)` within
        [Re(finite) − env, Re(finite) + env]  ×  [Im(finite) − env, Im(finite) + env].
    (`stirlingFinite`-style, mirroring `StirlingBinet.logDeriv_gammaR_enclosure`.) -/











end ZetaReflection


/-  EMZetaComplex.lean -- A2 Theorem 1, E-track: the COMPLEX Euler-Maclaurin representation of ζ
    and its K=1 analytic continuation into the critical strip.

    Builds on `EMZeta.lean` (real-s EM chain, Parts A-D', kernel-clean).  This file is the
    complex lift and the analytic continuation:

      E1.  `em_unit_step_cpow`   -- one-step EM over [m,m+1] for a ℂ-valued C¹ function.
           `em_cpow_partial`      -- finite-N EM for `f x = (x:ℂ)^(-s)`, s : ℂ, on [1,N].
      E2.  `em_zeta_cpow`         -- N→∞ complex representation, valid Re s > 1, tied to riemannZeta.
      E3.  `em_zeta_strip`        -- K=1 analytic continuation to 0 < Re s (s ≠ 1) with explicit
                                     remainder bound (THE PRIZE — covers the critical strip).
      E4.  `em_zeta_strip_enclosure` -- evaluator-facing finite-sum + explicit-tail enclosure shape.

    Only fully-proven, sorry-free lemmas live here.  General-K (K ≥ 2) stays in EMZetaWip.lean.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin + identity
    theorem), NOT a proof of RH.
-/




open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

/-! ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/



/-! ## E1b. Summed complex EM over an integer window, and the partial-ζ identity.

    Lift of `euler_maclaurin_one_window` to ℂ-valued `f`.  The telescoping and per-cell
    integrability arguments are identical to the real proof; the trapezoid bookkeeping is over ℂ. -/








theorem solution {s : ℂ} (hs : s ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
        - (((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2
        + ∫ x in (1 : ℝ)..N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hderiv : ∀ x ∈ Icc ((1 : ℕ) : ℝ) N,
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by have := hx.1; push_cast at this; linarith
    exact hasDerivAt_cpow_neg hs (lt_of_lt_of_le zero_lt_one hx1)
  have hf'int : ∀ k ∈ Finset.Ico 1 N,
      IntervalIntegrable (fun x => -s * (x : ℂ) ^ (-s - 1)) volume (k : ℝ) (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.mul continuousOn_const
    -- `x ↦ (x:ℂ)^(-s-1)` is continuous on `[k, k+1]` (arg bounded away from 0, in slitPlane).
    apply ContinuousOn.cpow_const
    · exact Complex.continuous_ofReal.continuousOn
    · intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans hk1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
  have hEM := euler_maclaurin_one_window_cpow (f := fun x => (x : ℂ) ^ (-s))
    (f' := fun x => -s * (x : ℂ) ^ (-s - 1)) 1 N hN hderiv hf'int
  simpa using hEM
