-- Prove2me | solution 1 for ZetaReflection.em_zeta_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:01:37.091142+00:00
-- url     : https://prove2.me/submissions/f63010b5-13f6-40e7-bebc-86da06e1b27f

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
import Theorems.Thm_ZetaReflection_em_cpow_partial
import Theorems.Thm_ZetaReflection_em_cpow_remainder_integrableOn
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

/-- The complex `x^{-s}` is integrable on `(1, ∞)` for `Re s > 1`: its norm is `x^{-Re s}`,
    integrable there since `-Re s < -1`. -/
theorem cpow_neg_integrableOn_Ioi {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-s)) (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.pow_const _)
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-s.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -s.re) (c := (1 : ℝ)) (by linarith) (by norm_num)
  refine (integrable_norm_iff hmeas).mp ?_
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.neg_re]







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









/-! ## E2. The `N → ∞` complex representation for `Re s > 1`, tied to `riemannZeta`.

    Lift of `em_zeta_real` (Part D').  The three limits: partial sum → tsum (`summable_one_div_
    nat_cpow`), the two finite integrals → improper (`intervalIntegral_tendsto_integral_Ioi`),
    endpoint `N^{-s} → 0` (norm → 0).  Then `zeta_eq_tsum_one_div_nat_cpow` ties it to `ζ`. -/






theorem solution {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s))
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) + ((1 : ℝ) : ℂ) ^ (-s) / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hI : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) := cpow_neg_integrableOn_Ioi hs
  have hR := em_cpow_remainder_integrableOn hs
  have hsummable : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    have hsm := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    refine hsm.congr (fun n => ?_)
    rw [Complex.cpow_neg, one_div]
  have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  -- LHS: partial sum over `Ico 1 N` → the tsum.
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (∑' n : ℕ, (n : ℂ) ^ (-s))) := by
    have hrange : (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        = (fun N : ℕ => ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s)) := by
      funext N
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun n => (n : ℂ) ^ (-s))
            (Nat.zero_le 1) (by lia : 1 ≤ N), Nat.Ico_zero_eq_range, Finset.sum_range_one,
            h0, zero_add]
    rw [hrange]; exact hsummable.hasSum.tendsto_sum_nat
  -- RHS component limits.
  have hA : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hI tendsto_natCast_atTop_atTop
  have hEnd : Tendsto (fun N : ℕ => -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)) atTop
      (𝓝 (((1 : ℝ) : ℂ) ^ (-s) / 2)) := by
    have hz : Tendsto (fun N : ℕ => (((N : ℝ) : ℂ)) ^ (-s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : (fun N : ℕ => ‖(((N : ℝ) : ℂ)) ^ (-s)‖)
          =ᶠ[atTop] (fun N : ℕ => (N : ℝ) ^ (-s.re)) := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN), Complex.neg_re]
      refine Tendsto.congr' hnorm.symm ?_
      exact (tendsto_rpow_neg_atTop (y := s.re) (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := ((hz.sub_const (((1 : ℝ) : ℂ) ^ (-s))).div_const 2).neg
    convert h2 using 2; ring
  have hRem : Tendsto
      (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hR tendsto_natCast_atTop_atTop
  have hEq : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
        + -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := em_cpow_partial hs0 (N := N) hN
    rw [hp]; ring
  have hRHS := (hA.add hEnd).add hRem
  have hLHS' : Tendsto (fun N : ℕ =>
      (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
        + -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) atTop
      (𝓝 (∑' n : ℕ, (n : ℂ) ^ (-s))) := hLHS.congr' hEq
  exact tendsto_nhds_unique hLHS' hRHS
