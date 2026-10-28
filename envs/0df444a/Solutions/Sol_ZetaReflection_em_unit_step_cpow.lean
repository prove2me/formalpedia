-- Prove2me | solution 1 for ZetaReflection.em_unit_step_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:51:50.246897+00:00
-- url     : https://prove2.me/submissions/67fa0e07-b0f0-4006-b0f9-55d857e04d3c

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

/-- The order-1 saw on the cell `[m, m+1)` is the affine sawtooth `x - m - 1/2`. -/
lemma sawBernoulli_one_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 1 x = x - m - 1 / 2 := by
  rw [sawBernoulli_eq_on_Ico 1 hx, bernoulliFun_one]

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

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

/-! ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/


theorem solution {f f' : ℝ → ℂ} (m : ℤ)
    (hf : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), f x)
      = (f m + f (m + 1)) / 2
        - ∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x := by
  -- The affine antiderivative `w x = x - m - 1/2` of the constant `1`, valued in ℂ.
  set w : ℝ → ℂ := fun x => (x : ℂ) - m - 1 / 2 with hw
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hw' : ∀ x, HasDerivAt w 1 x := by
    intro x
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have := (hbase.sub_const (m : ℂ)).sub_const (1 / 2 : ℂ)
    simpa [hw] using this
  have hwcont : Continuous w := by fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt w (1 : ℂ) x := fun x _ => hw' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hf x hx
  have hw'int : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  have hIBP := integral_deriv_mul_eq_sub huv hfd hw'int hf'
  have hwL : w (m : ℝ) = -(1 / 2) := by simp only [hw]; push_cast; ring
  have hwR : w ((m : ℝ) + 1) = 1 / 2 := by simp only [hw]; push_cast; ring
  have hwf'int : IntervalIntegrable (fun x => w x * f' x) volume (m : ℝ) (m + 1) :=
    hf'.continuousOn_mul hwcont.continuousOn
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (1 : ℂ) * f x + w x * f' x)
        = (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    have hfcont : ContinuousOn f (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    have hfint : IntervalIntegrable f volume (m : ℝ) (m + 1) :=
      hfcont.intervalIntegrable
    rw [intervalIntegral.integral_add (by simpa using hfint) hwf'int]
    simp
  -- Identify `(sawBernoulli 1 · : ℂ) · f'` with `w · f'` a.e. on the cell.
  have hsaw : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    simp only [hw]; push_cast; ring
  rw [hsaw]
  have key : (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x
      = w ((m : ℝ) + 1) * f ((m : ℝ) + 1) - w (m : ℝ) * f (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hwL, hwR] at key
  -- Solve for `∫ f` (ℂ is not ordered — use `linear_combination`).
  linear_combination key
