-- Prove2me | solution 1 for RSDesignTheta.secant_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:47:55.488958+00:00
-- url     : https://prove2.me/submissions/b27dab60-85f8-442e-a106-d0853ae9cd77

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


theorem solution {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ u ∈ Icc a b, HasDerivAt f (g u) u) (hg : MonotoneOn g (Icc a b))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    (v - u) * g u ≤ f v - f u ∧ f v - f u ≤ (v - u) * g v := by
  rcases eq_or_lt_of_le huv with h | h
  · subst h; simp
  · have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hcont : ContinuousOn f (Icc u v) := fun w hw =>
      (hf w (hsub hw)).continuousAt.continuousWithinAt
    have hderiv : ∀ w ∈ Ioo u v, HasDerivAt f (g w) w := fun w hw =>
      hf w (hsub (Ioo_subset_Icc_self hw))
    obtain ⟨c, hc, hgc⟩ := exists_hasDerivAt_eq_slope f g h hcont hderiv
    have hcI : c ∈ Icc a b := hsub (Ioo_subset_Icc_self hc)
    have h1 : g u ≤ g c := hg hu hcI hc.1.le
    have h2 : g c ≤ g v := hg hcI hv hc.2.le
    have hpos : 0 < v - u := sub_pos.mpr h
    rw [hgc] at h1 h2
    have h1' := (le_div_iff₀ hpos).mp h1
    have h2' := (div_le_iff₀ hpos).mp h2
    constructor <;> nlinarith [h1', h2']
