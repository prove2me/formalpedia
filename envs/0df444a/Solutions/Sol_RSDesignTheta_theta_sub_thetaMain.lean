-- Prove2me | solution 1 for RSDesignTheta.theta_sub_thetaMain
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:56:27.64427+00:00
-- url     : https://prove2.me/submissions/8886f9d8-f2ff-4ba7-8573-8e93ab3ff7fe

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
import Theorems.Thm_RSDesignTheta_theta_bracket
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





/-! ## 5.  The Riemann-Siegel phase: the `n0 = 0`, `x = 1/4`, `y = t/2` specialisation. -/






theorem solution (t : ℝ) (ht : 0 < t) (Λ : ℝ)
    (hΛ : Tendsto (imLnVal (1/4) (t/2)) atTop (𝓝 Λ)) :
    |Λ - t / 2 * Real.log Real.pi - ZeroFreeBridge.thetaMain t| ≤ 1 / t := by
  have hb := theta_bracket t ht Λ hΛ
  unfold thetaS at hb
  unfold ZeroFreeBridge.thetaMain
  set v : ℝ := 1 / (4 * t ^ 2) with hv
  have hv0 : 0 ≤ v := by positivity
  have hlog : Real.log (1 / 16 + t ^ 2 / 4)
      = 2 * Real.log t - 2 * Real.log 2 + Real.log (1 + v) := by
    have h1 : (1 / 16 + t ^ 2 / 4 : ℝ) = (t ^ 2 / 2 ^ 2) * (1 + v) := by
      rw [hv]; field_simp; ring
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have harc : Real.arctan (2 * t) = Real.pi / 2 - Real.arctan (1 / (2 * t)) := by
    have h := Real.arctan_inv_of_pos (by positivity : (0:ℝ) < 2 * t)
    rw [inv_eq_one_div] at h
    linarith
  have hL0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hL1 : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos (x := 1 + v) (by linarith)
    linarith
  have hA0 : 0 ≤ Real.arctan (1 / (2 * t)) := by
    have : (0:ℝ) ≤ 1 / (2 * t) := by positivity
    exact Real.arctan_nonneg.mpr this
  have hA1 : Real.arctan (1 / (2 * t)) ≤ 1 / (2 * t) :=
    ArctanTaylor.arctan_le_self (by positivity)
  have hP0 : 0 ≤ t / 4 * Real.log (1 + v) := by positivity
  have hP1 : t / 4 * Real.log (1 + v) ≤ 1 / (16 * t) := by
    have h := mul_le_mul_of_nonneg_left hL1 (by positivity : (0:ℝ) ≤ t / 4)
    have he : t / 4 * v = 1 / (16 * t) := by rw [hv]; field_simp; ring
    linarith
  have hq1 : 1 / (2 * t) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht]; linarith
  have hq2 : 1 / (16 * t) + 1 / 4 * (1 / (2 * t)) ≤ 1 / t := by
    have e : 1 / (16 * t) + 1 / 4 * (1 / (2 * t)) = (3 / 16) * (1 / t) := by field_simp; ring
    have : 0 ≤ 1 / t := by positivity
    rw [e]; linarith
  rw [hlog, harc] at hb
  rw [hlog2pi, abs_le]
  constructor <;> nlinarith [hb.1, hb.2, hP0, hP1, hA0, hA1, hq1, hq2]
