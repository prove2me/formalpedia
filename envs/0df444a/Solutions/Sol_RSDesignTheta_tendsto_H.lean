-- Prove2me | solution 1 for RSDesignTheta.tendsto_H
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:48:16.263617+00:00
-- url     : https://prove2.me/submissions/c36fb633-f346-4f4c-9747-c3f8875af66f

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Theorems.Thm_ArctanTaylor_arctan_le_self
import Theorems.Thm_ArctanTaylor_self_sub_cube_le_arctan
namespace ThetaGap
end ThetaGap

/-  RSTheta.lean -- ANDURIL Riemann-Siegel brick B0 (theta): a HEIGHT-UNIFORM kernel enclosure of
    the Riemann-Siegel phase, plus one instance at t = 280000.

    ## Provenance

    Promoted on 2026-09-23 from `Probes/RSDesign_theta.lean`, the calibration probe of the RS design
    memo (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 4.0 and op O-4). Every proof is
    unchanged. Two things differ from the probe:

      * The statement of the registry theorem `gaussBranch_theta_sub_thetaMain_le` now spells every
        name in full: `Filter.Tendsto`, `ThetaGap.imLnVal`, `Filter.atTop`, `nhds`. That makes it the
        verbatim text of the proposed `AND_theta_branch` statement (memo op O-4). The grant gate
        matches statement to artifact by normalized text, and the registry statement cannot rely on
        this file's `open` lines. Both spellings elaborate to the same term.
      * The trailing `#print axioms` lines moved to the guard `AxiomGuardRSTheta.lean`.

    The namespace stays `RSDesignTheta`, so names cited from the probe still resolve.

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms).

    The island's sign bridge `ZeroSignDecomp.gLine_sign_decomp_t` writes
        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,
        phi = Lam - (t/2) log pi,   Lam = lim_n imLnVal (1/4) (t/2) n,
    so every on-line sign needs a box for `phi` (= the Riemann-Siegel theta).  The existing route
    (`ForgeRate.rate_at`) bounds `|Lam - imLnVal x y n0|` by `2(|y|(x+1) + |y|^3/(3 n0))/n0`, which needs
    `n0 >> y^(3/2)` arctan terms: about 10^9 terms at t = 280000.  That is the "theta Euler route
    dies above a few hundred" wall.

    This file replaces the rate bound by a CLOSED-FORM Stirling bracket with an explicit remainder,
    valid at EVERY height, proved by an elementary convex-trapezoid argument (no Bernoulli
    functions, no polygamma, no complex Stirling, no Mathlib gap):

      * `trapezoid_convex`   : for F' = f, f' = g, g monotone on [a, a+1]:
                               0 <= (f a + f (a+1))/2 - (F (a+1) - F a) <= (g (a+1) - g a)/4.
      * `lam_bracket`        : for x > 0, y >= 0, any n0, and Lam = lim imLnVal x y:
            C - y/(4((x+n0)^2 + y^2)) <= Lam <= C,
            C = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k - y,
            fA u = arctan (y/(x+u)),  FA u = (x+u) arctan (y/(x+u)) + (y/2) log ((x+u)^2 + y^2).
      * `theta_bracket`      : n0 = 0, x = 1/4, y = t/2, for every t > 0:
            thetaS t - 1/(2t) <= Lam - (t/2) log pi <= thetaS t,
            thetaS t = (t/4) log (1/16 + t^2/4) - (1/4) arctan (2t) - t/2 - (t/2) log pi.
      * `theta_sub_thetaMain`, `gaussBranch_theta_sub_thetaMain_le` : against the corpus main term
            `ZeroFreeBridge.thetaMain`, |Lam - (t/2) log pi - thetaMain t| <= 1/t for every t > 0 --
            the statement DESIGN_AND_ladder_1e9 section 3.3 proposed for `AND_theta_branch` (there with
            t >= 200 and the misspelled `ZetaReflection.imLnVal`; the island name is `ThetaGap.imLnVal`).
      * `theta_280000_box`   : the numeric instance at t = 280000 (reduced mod 2 pi, K = 216236),
                               an interval of width about 2e-6 around 2.2434215934
                               (mpmath siegeltheta(280000) - 2 pi K = 2.2434215934093).

    So the theta brick of the RS era costs O(1) transcendental evaluations per point at any height
    (two logs, one arctan, log pi shared), instead of O(t^(3/2)) arctan terms.  The general
    `lam_bracket` (any x > 0) also covers the Gamma_R edge quantities Im log Gamma(x + iT/2) at
    x = 1 (sigma = 2) and, after one shift Gamma(z) = Gamma(z+1)/z, at sigma = -1.

    Calibration (the probe, 2026-09-23): 646 lines, two compile iterations. `lake env lean` took about
    20 s wall, of which kernel type checking was 0.33 s and `norm_num` elaboration 4.7 s.

    conjecture1_proved = False.  A finite enclosure of one special-function value plus a
    height-uniform inequality; nothing here bears on the Riemann Hypothesis.
-/



open Real Filter Topology Set ThetaGap

section
namespace RSDesignTheta
end RSDesignTheta
open RSDesignTheta

/-! ## 1.  The convex trapezoid lemma. -/





/-! ## 2.  The θ-series summand, its antiderivative and derivative. -/















/-! ## 3.  The finite sandwich of `imLnVal`. -/











/-! ## 4.  The limit of `H n` and the Stirling bracket for `Lam`. -/

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    Tendsto (fun n : ℕ => y * Real.log n - FA x y n - fA x y n / 2) atTop (𝓝 (-y)) := by
  -- (a) the log part
  have hx0 : Tendsto (fun n : ℕ => x / (n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat x
  have hy0 : Tendsto (fun n : ℕ => y / (n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat y
  have hq : Tendsto (fun n : ℕ => (1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2) atTop
      (𝓝 ((1 + 0) ^ 2 + 0 ^ 2)) :=
    ((hx0.const_add 1).pow 2).add (hy0.pow 2)
  have hq1 : ((1:ℝ) + 0) ^ 2 + 0 ^ 2 = 1 := by norm_num
  rw [hq1] at hq
  have hlogq : Tendsto (fun n : ℕ => Real.log ((1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2)) atTop
      (𝓝 (Real.log 1)) :=
    ((Real.continuousAt_log (by norm_num)).tendsto).comp hq
  rw [Real.log_one] at hlogq
  have hA : Tendsto (fun n : ℕ => y * Real.log n - y / 2 * Real.log ((x + n) ^ 2 + y ^ 2))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => -(y / 2) * Real.log ((1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2))
        atTop (𝓝 (-(y / 2) * 0)) := hlogq.const_mul _
    rw [mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hfac : (x + n) ^ 2 + y ^ 2 = (n:ℝ) ^ 2 * ((1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2) := by
      field_simp
      ring
    have hqpos : 0 < (1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2 := by
      have : 0 < 1 + x / (n:ℝ) := by positivity
      positivity
    rw [hfac, Real.log_mul (by positivity) hqpos.ne', Real.log_pow]
    push_cast
    ring
  -- (b) the arctan argument tends to 0
  have hden : Tendsto (fun n : ℕ => x + (n:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hu0 : Tendsto (fun n : ℕ => y / (x + (n:ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hC : Tendsto (fun n : ℕ => fA x y n) atTop (𝓝 0) := by
    have := ((Real.continuous_arctan.tendsto 0).comp hu0)
    rw [Real.arctan_zero] at this
    exact this
  -- (c) (x+n) arctan (y/(x+n)) -> y by squeezing
  have hB : Tendsto (fun n : ℕ => (x + n) * Real.arctan (y / (x + n))) atTop (𝓝 y) := by
    have hlow : Tendsto (fun n : ℕ => y - (y ^ 3 / 3) / (n:ℝ)) atTop (𝓝 (y - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [sub_zero] at hlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hxn : 0 < x + n := by linarith
      set u : ℝ := y / (x + n) with hu
      have hu0' : 0 ≤ u := by positivity
      have hcube := ArctanTaylor.self_sub_cube_le_arctan hu0'
      have hxu : (x + n) * u = y := by rw [hu]; field_simp
      have hmul : (x + n) * (u - u ^ 3 / 3) ≤ (x + n) * Real.arctan u :=
        mul_le_mul_of_nonneg_left hcube hxn.le
      have hid : (x + n) * (u - u ^ 3 / 3) = y - y ^ 3 / (3 * (x + n) ^ 2) := by
        rw [hu]; field_simp
      have hsmall : y ^ 3 / (3 * (x + n) ^ 2) ≤ (y ^ 3 / 3) / (n:ℝ) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hxn : 0 < x + n := by linarith
      set u : ℝ := y / (x + n) with hu
      have hu0' : 0 ≤ u := by positivity
      have hle := ArctanTaylor.arctan_le_self hu0'
      have hxu : (x + n) * u = y := by rw [hu]; field_simp
      have := mul_le_mul_of_nonneg_left hle hxn.le
      linarith
  -- assemble: H = A - B - C/2
  have hsum : Tendsto (fun n : ℕ => (y * Real.log n - y / 2 * Real.log ((x + n) ^ 2 + y ^ 2))
      - (x + n) * Real.arctan (y / (x + n)) - fA x y n / 2) atTop (𝓝 (0 - y - 0 / 2)) :=
    (hA.sub hB).sub (hC.div_const 2)
  have hval : (0:ℝ) - y - 0 / 2 = -y := by ring
  rw [hval] at hsum
  refine hsum.congr' (Eventually.of_forall fun n => ?_)
  unfold FA
  ring
