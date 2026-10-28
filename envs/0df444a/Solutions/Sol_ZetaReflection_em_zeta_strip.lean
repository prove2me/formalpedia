-- Prove2me | solution 1 for ZetaReflection.em_zeta_strip
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:04:21.555531+00:00
-- url     : https://prove2.me/submissions/7fbfc5aa-89ec-4f0e-9210-dd9d68c49969

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
import Theorems.Thm_ZetaReflection_emZetaClosed_analyticOnNhd
import Theorems.Thm_ZetaReflection_emZetaClosed_eq_riemannZeta_of_one_lt
import Theorems.Thm_ZetaReflection_isPreconnected_rightHalfPlane_diff_one
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











/-! ### The critical-strip half-plane, slit at `1`, is preconnected. -/





/-! ### E3 capstone: the identity theorem transfer. -/



/-- `riemannZeta` is analytic on the slit half-plane `{Re s > 0} \ {1}` (it is analytic on all of
    `{1}ᶜ`). -/
theorem riemannZeta_analyticOnNhd_strip :
    AnalyticOnNhd ℂ riemannZeta (rightHalfPlane \ {1}) := by
  apply DifferentiableOn.analyticOnNhd _ ?_
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt
  · apply IsOpen.sdiff _ isClosed_singleton
    exact (isOpen_lt continuous_const Complex.continuous_re)



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











/-! ### The critical-strip half-plane, slit at `1`, is preconnected. -/





/-! ### E3 capstone: the identity theorem transfer. -/






theorem solution {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s
      = 1 / (s - 1) + 1 / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  -- reduce to `emZetaClosed s = riemannZeta s`.
  suffices h : Set.EqOn emZetaClosed riemannZeta (rightHalfPlane \ {1}) by
    have hmem : s ∈ rightHalfPlane \ {1} := ⟨hs, by simpa using hs1⟩
    have heq := h hmem
    rw [emZetaClosed, emZetaRemainder] at heq
    exact heq.symm
  -- identity theorem, anchored at s = 2.
  have h2mem : (2 : ℂ) ∈ rightHalfPlane \ {1} := by
    refine ⟨?_, ?_⟩ <;> simp [rightHalfPlane]
  have hevent : emZetaClosed =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      hopen.mem_nhds (by simp)
    filter_upwards [hnhds] with z hz
    exact emZetaClosed_eq_riemannZeta_of_one_lt hz
  exact emZetaClosed_analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    riemannZeta_analyticOnNhd_strip isPreconnected_rightHalfPlane_diff_one h2mem hevent
