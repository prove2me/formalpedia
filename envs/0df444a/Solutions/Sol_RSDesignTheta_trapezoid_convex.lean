-- Prove2me | solution 1 for RSDesignTheta.trapezoid_convex
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:49:52.775223+00:00
-- url     : https://prove2.me/submissions/d1712652-93e1-44a3-91f4-822cf475c3fc

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
import Theorems.Thm_RSDesignTheta_secant_bounds
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




theorem solution {f F g : ℝ → ℝ} {a : ℝ}
    (hF : ∀ u ∈ Icc a (a + 1), HasDerivAt F (f u) u)
    (hf : ∀ u ∈ Icc a (a + 1), HasDerivAt f (g u) u)
    (hg : MonotoneOn g (Icc a (a + 1))) :
    0 ≤ (f a + f (a + 1)) / 2 - (F (a + 1) - F a) ∧
      (f a + f (a + 1)) / 2 - (F (a + 1) - F a) ≤ (g (a + 1) - g a) / 4 := by
  have hmem : ∀ h ∈ Icc (0:ℝ) 1, a + h ∈ Icc a (a + 1) := fun h hh =>
    ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have haI : a ∈ Icc a (a + 1) := ⟨le_refl a, by linarith⟩
  have ha1I : a + 1 ∈ Icc a (a + 1) := ⟨by linarith, le_refl _⟩
  -- derivative of the shifted functions
  have hfs : ∀ h ∈ Icc (0:ℝ) 1, HasDerivAt (fun h => f (a + h)) (g (a + h)) h := by
    intro h hh
    have h1 : HasDerivAt (fun h => a + h) 1 h := (hasDerivAt_id' h).const_add a
    exact ((hf (a + h) (hmem h hh)).comp h h1).congr_deriv (mul_one _)
  have hFs : ∀ h ∈ Icc (0:ℝ) 1, HasDerivAt (fun h => F (a + h)) (f (a + h)) h := by
    intro h hh
    have h1 : HasDerivAt (fun h => a + h) 1 h := (hasDerivAt_id' h).const_add a
    exact ((hF (a + h) (hmem h hh)).comp h h1).congr_deriv (mul_one _)
  -- φ(h) = h (f a + f (a+h))/2 - (F (a+h) - F a)
  set φ : ℝ → ℝ := fun h => h * (f a + f (a + h)) / 2 - (F (a + h) - F a) with hφdef
  have hφd : ∀ h ∈ Icc (0:ℝ) 1,
      HasDerivAt φ ((f a - f (a + h)) / 2 + h * g (a + h) / 2) h := by
    intro h hh
    have hA : HasDerivAt (fun h => h * (f a + f (a + h)))
        (1 * (f a + f (a + h)) + h * g (a + h)) h :=
      (hasDerivAt_id' h).mul ((hfs h hh).const_add (f a))
    have hB := (hA.div_const 2).sub ((hFs h hh).sub_const (F a))
    exact hB.congr_deriv (by ring)
  -- secant facts at (a, a+h)
  have hsec : ∀ h ∈ Icc (0:ℝ) 1,
      h * g a ≤ f (a + h) - f a ∧ f (a + h) - f a ≤ h * g (a + h) := by
    intro h hh
    have := secant_bounds hf hg haI (hmem h hh) (by linarith [hh.1])
    simpa using this
  -- monotonicity of φ on [0,1]
  have hφmono : MonotoneOn φ (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · exact fun h hh => (hφd h hh).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact (hφd h (Ioo_subset_Icc_self hh)).hasDerivWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have := (hsec h (Ioo_subset_Icc_self hh)).2
      linarith
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  have hφ1 : φ 1 = (f a + f (a + 1)) / 2 - (F (a + 1) - F a) := by simp [hφdef]
  have hlow : φ 0 ≤ φ 1 :=
    hφmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  -- ψ(h) = h^2 (g (a+1) - g a)/4 - φ h
  set D : ℝ := g (a + 1) - g a with hD
  set ψ : ℝ → ℝ := fun h => h ^ 2 * D / 4 - φ h with hψdef
  have hψd : ∀ h ∈ Icc (0:ℝ) 1,
      HasDerivAt ψ (2 * h * D / 4 - ((f a - f (a + h)) / 2 + h * g (a + h) / 2)) h := by
    intro h hh
    have hA : HasDerivAt (fun h : ℝ => h ^ 2 * D / 4) (2 * h * D / 4) h := by
      have := ((hasDerivAt_pow 2 h).mul_const D).div_const 4
      exact this.congr_deriv (by push_cast; ring)
    exact hA.sub (hφd h hh)
  have hψmono : MonotoneOn ψ (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · exact fun h hh => (hψd h hh).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact (hψd h (Ioo_subset_Icc_self hh)).hasDerivWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have hhI : h ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hh
      have hs1 := (hsec h hhI).1
      have hgmono : g (a + h) ≤ g (a + 1) := hg (hmem h hhI) ha1I (by linarith [hh.2])
      have hprod : 0 ≤ h * (g (a + 1) - g (a + h)) :=
        mul_nonneg hh.1.le (by linarith)
      rw [hD]
      nlinarith [hs1, hprod]
  have hψ0 : ψ 0 = 0 := by simp [hψdef, hφ0]
  have hup : ψ 0 ≤ ψ 1 :=
    hψmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have hψ1 : ψ 1 = D / 4 - φ 1 := by simp [hψdef]
  constructor
  · rw [← hφ1]; linarith
  · rw [← hφ1]; linarith
