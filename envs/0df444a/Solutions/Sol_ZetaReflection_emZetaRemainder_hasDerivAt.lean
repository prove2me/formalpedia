-- Prove2me | solution 1 for ZetaReflection.emZetaRemainder_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:36.082537+00:00
-- url     : https://prove2.me/submissions/6d22f839-9660-466b-af65-73b5295f6166

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
import Theorems.Thm_ZetaReflection_em_cpow_remainder_integrableOn_strip
import Theorems.Thm_ZetaReflection_hasDerivAt_emIntegrand
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

/-- The order-1 saw is bounded by `1/2` (it is `{x} − 1/2` with `{x} ∈ [0, 1)`). -/
lemma abs_sawBernoulli_one_le (x : ℝ) : |sawBernoulli 1 x| ≤ 1 / 2 := by
  rw [sawBernoulli, bernoulliFun_one, abs_le]
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  constructor <;> linarith





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

/-- Elementary global bound `log x ≤ x^δ / δ` for `x ≥ 1`, `δ > 0` (log grows slower than any
    positive power).  `δ·log x = log(x^δ) ≤ x^δ − 1 ≤ x^δ`. -/
theorem log_le_rpow_div {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ x ^ δ / δ := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : δ * Real.log x = Real.log (x ^ δ) := (Real.log_rpow hxpos δ).symm
  have hxδpos : (0 : ℝ) < x ^ δ := Real.rpow_pos_of_pos hxpos δ
  have hle : Real.log (x ^ δ) ≤ x ^ δ - 1 := Real.log_le_sub_one_of_pos hxδpos
  rw [le_div_iff₀ hδ]
  calc Real.log x * δ = δ * Real.log x := by ring
    _ = Real.log (x ^ δ) := hlog
    _ ≤ x ^ δ - 1 := hle
    _ ≤ x ^ δ := by linarith



/-- Integrability on `(1,∞)` of the dominating bound `C · x^{−σ−1} + D · x^{δ−σ−1}` used for
    differentiation under the integral, when `0 < δ < σ` (so both exponents are `< −1`). -/
private theorem bound_integrableOn {C D σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ < σ) :
    IntegrableOn (fun x : ℝ => C * x ^ (-σ - 1) + D * x ^ (δ - σ - 1)) (Ioi 1) := by
  have h1 : IntegrableOn (fun x : ℝ => C * x ^ (-σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (by linarith) (by norm_num : (0:ℝ) < 1)).const_mul _
  have h2 : IntegrableOn (fun x : ℝ => D * x ^ (δ - σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := δ - σ - 1) (by linarith) (by norm_num : (0:ℝ) < 1)).const_mul _
  exact h1.add h2





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








theorem solution {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    HasDerivAt emZetaRemainder
      (∫ x in Ioi (1 : ℝ),
        (sawBernoulli 1 x : ℂ) * ((-1 + s₀ * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s₀ - 1))) s₀ := by
  set σ : ℝ := s₀.re / 2 with hσdef
  set ε : ℝ := s₀.re / 2 with hεdef
  set δ : ℝ := σ / 2 with hδdef
  have hσpos : 0 < σ := by rw [hσdef]; linarith
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδσ : δ < σ := by rw [hδdef]; linarith
  -- The ball `s` region and the re-lower-bound on it.
  set S : Set ℂ := Metric.ball s₀ ε with hSdef
  have hS_nhds : S ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ hεpos
  have hre_lb : ∀ s ∈ S, σ ≤ s.re := by
    intro s hs
    rw [hSdef, Metric.mem_ball] at hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have h2 : ‖s - s₀‖ < ε := by rwa [Complex.dist_eq] at hs
    have : |s.re - s₀.re| < ε := lt_of_le_of_lt h1 h2
    have := (abs_lt.mp this).1
    rw [hσdef, hεdef]; rw [hεdef] at this; linarith
  -- Integrand F and derivative F'.
  set F : ℂ → ℝ → ℂ := fun s x => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) with hFdef
  set F' : ℂ → ℝ → ℂ := fun s x =>
    (sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)) with hF'def
  -- The dominating bound.
  set bnd : ℝ → ℝ := fun x => (1 / 2) * x ^ (-σ - 1)
    + ((1 / 2) * (‖s₀‖ + ε) * (1 / δ)) * x ^ (δ - σ - 1) with hbnddef
  -- (a) measurability of F near s₀
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) (volume.restrict (Ioi 1)) := by
    filter_upwards with s
    apply Measurable.aestronglyMeasurable
    rw [hFdef]
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  -- (b) F s₀ integrable
  have hF_int : Integrable (F s₀) (volume.restrict (Ioi 1)) :=
    em_cpow_remainder_integrableOn_strip hs₀
  -- (c) F' s₀ measurable
  have hF'_meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    rw [hF'def]
    apply (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
    apply Measurable.mul
    · exact measurable_const.add (measurable_const.mul
        (Complex.measurable_log.comp Complex.measurable_ofReal))
    · exact Complex.measurable_ofReal.pow_const _
  -- (d) uniform bound on S
  have h_bound : ∀ᵐ x ∂(volume.restrict (Ioi 1)), ∀ s ∈ S, ‖F' s x‖ ≤ bnd x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx s hs
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hsre : σ ≤ s.re := hre_lb s hs
    have hslt : ‖s‖ ≤ ‖s₀‖ + ε := by
      have : ‖s - s₀‖ < ε := by rw [hSdef, Metric.mem_ball, Complex.dist_eq] at hs; exact hs
      calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₀‖ + ε := by linarith
    -- ‖F' s x‖ = |saw|·‖(-1 + s log x)·x^{-s-1}‖ ≤ (1/2)·(1 + ‖s‖ log x)·x^{-σ-1}
    have hlogeq : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hxpos.le).symm
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hcpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    have hsaw := abs_sawBernoulli_one_le x
    -- factor bound
    have hfac : ‖(-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
      rw [norm_mul, hnormcpow]
      gcongr
      calc ‖(-1 + s * Complex.log (x : ℂ))‖
          ≤ ‖(-1 : ℂ)‖ + ‖s * Complex.log (x : ℂ)‖ := norm_add_le _ _
        _ = 1 + ‖s‖ * ‖Complex.log (x : ℂ)‖ := by rw [norm_mul]; norm_num
        _ = 1 + ‖s‖ * Real.log x := by
            rw [hlogeq, Complex.norm_real, Real.norm_of_nonneg hlognn]
    -- log bound: log x ≤ x^δ / δ
    have hlogbd : Real.log x ≤ x ^ δ / δ := log_le_rpow_div hδpos hx1
    have hxδdivnn : (0 : ℝ) ≤ x ^ δ / δ := by positivity
    have hs₀εnn : (0 : ℝ) ≤ ‖s₀‖ + ε := by positivity
    have hexpmono : x ^ (-s.re - 1) ≤ x ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hcpowσnn : (0 : ℝ) ≤ x ^ (-σ - 1) := Real.rpow_nonneg hxpos.le _
    rw [hF'def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |sawBernoulli 1 x| * ‖(-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (1 / 2) * ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) := by
          gcongr
      _ ≤ (1 / 2) * ((1 + (‖s₀‖ + ε) * (x ^ δ / δ)) * x ^ (-σ - 1)) := by
          gcongr
      _ = bnd x := by
          have hxadd : x ^ (δ - σ - 1) = x ^ δ * x ^ (-σ - 1) := by
            rw [← Real.rpow_add hxpos]; congr 1; ring
          have hδne : δ ≠ 0 := ne_of_gt hδpos
          simp only [hbnddef, hxadd]
          field_simp
  -- Assemble via the parametric-integral differentiation lemma.
  have hbnd_int : Integrable bnd (volume.restrict (Ioi 1)) := by
    rw [hbnddef]
    exact bound_integrableOn (C := 1 / 2) (D := (1 / 2) * (‖s₀‖ + ε) * (1 / δ))
      hσpos hδpos hδσ
  have h_diff : ∀ᵐ x ∂(volume.restrict (Ioi 1)), ∀ s ∈ S, HasDerivAt (fun s => F s x) (F' s x) s := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx s _
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_of_lt hx)
    exact hasDerivAt_emIntegrand x hxpos s
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bnd) (F := F) (F' := F') hS_nhds hF_meas hF_int hF'_meas h_bound hbnd_int h_diff
  exact hderiv
