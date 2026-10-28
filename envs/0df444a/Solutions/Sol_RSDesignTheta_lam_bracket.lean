-- Prove2me | solution 1 for RSDesignTheta.lam_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:52:21.241554+00:00
-- url     : https://prove2.me/submissions/dc18f807-9592-4f0a-bf79-d9db38ca6cbe

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
import Theorems.Thm_RSDesignTheta_tendsto_H
import Theorems.Thm_RSDesignTheta_trapezoid_convex
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

namespace RSDesignTheta

/-! ## 1.  The convex trapezoid lemma. -/





/-! ## 2.  The θ-series summand, its antiderivative and derivative. -/







theorem hasDerivAt_fA (x y u : ℝ) (hxu : 0 < x + u) :
    HasDerivAt (fA x y) (gA x y u) u := by
  have hne : x + u ≠ 0 := hxu.ne'
  have hd : HasDerivAt (fun u => x + u) 1 u := (hasDerivAt_id' u).const_add x
  have hq : HasDerivAt (fun u => y / (x + u)) ((0 * (x + u) - y * 1) / (x + u) ^ 2) u :=
    (hasDerivAt_const u y).div hd hne
  have h := hq.arctan
  unfold fA gA
  refine h.congr_deriv ?_
  have hpos : 0 < (x + u) ^ 2 + y ^ 2 := by positivity
  field_simp
  ring

theorem hasDerivAt_FA (x y u : ℝ) (hxu : 0 < x + u) :
    HasDerivAt (FA x y) (fA x y u) u := by
  have hne : x + u ≠ 0 := hxu.ne'
  have hpos : 0 < (x + u) ^ 2 + y ^ 2 := by positivity
  have hd : HasDerivAt (fun u => x + u) 1 u := (hasDerivAt_id' u).const_add x
  have h1 : HasDerivAt (fun u => (x + u) * Real.arctan (y / (x + u)))
      (1 * Real.arctan (y / (x + u)) + (x + u) * gA x y u) u :=
    hd.mul (hasDerivAt_fA x y u hxu)
  have hsq : HasDerivAt (fun u => (x + u) ^ 2 + y ^ 2) (2 * (x + u)) u := by
    have := (hd.pow 2).add_const (y ^ 2)
    exact this.congr_deriv (by push_cast; ring)
  have h2 : HasDerivAt (fun u => y / 2 * Real.log ((x + u) ^ 2 + y ^ 2))
      (y / 2 * (2 * (x + u) / ((x + u) ^ 2 + y ^ 2))) u :=
    (hsq.log hpos.ne').const_mul (y / 2)
  have h := h1.add h2
  unfold FA fA
  refine h.congr_deriv ?_
  unfold gA
  field_simp
  ring

theorem gA_monotoneOn (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) : MonotoneOn (gA x y) (Ici 0) := by
  intro u hu v hv huv
  simp only [mem_Ici] at hu hv
  unfold gA
  have hu' : 0 < x + u := by linarith
  have hsq : (x + u) ^ 2 + y ^ 2 ≤ (x + v) ^ 2 + y ^ 2 := by nlinarith
  have hpu : 0 < (x + u) ^ 2 + y ^ 2 := by positivity
  have := div_le_div_of_nonneg_left hy hpu hsq
  linarith

theorem gA_nonpos (x y u : ℝ) (hy : 0 ≤ y) : gA x y u ≤ 0 := by
  unfold gA
  have : 0 ≤ y / ((x + u) ^ 2 + y ^ 2) := by positivity
  linarith

/-! ## 3.  The finite sandwich of `imLnVal`. -/



theorem eA_bounds (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (k : ℕ) :
    0 ≤ eA x y k ∧ eA x y k ≤ (gA x y ((k:ℝ) + 1) - gA x y k) / 4 := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hsub : Icc (k:ℝ) ((k:ℝ) + 1) ⊆ Ici 0 := fun u hu => le_trans hk hu.1
  have hF : ∀ u ∈ Icc (k:ℝ) ((k:ℝ) + 1), HasDerivAt (FA x y) (fA x y u) u := fun u hu =>
    hasDerivAt_FA x y u (by linarith [hu.1])
  have hf : ∀ u ∈ Icc (k:ℝ) ((k:ℝ) + 1), HasDerivAt (fA x y) (gA x y u) u := fun u hu =>
    hasDerivAt_fA x y u (by linarith [hu.1])
  have hg : MonotoneOn (gA x y) (Icc (k:ℝ) ((k:ℝ) + 1)) :=
    (gA_monotoneOn x y hx hy).mono hsub
  exact trapezoid_convex hF hf hg

/-- The telescoped split of the finite arctan sum at a base index `n0`. -/
theorem sum_split (x y : ℝ) (n0 : ℕ) :
    ∀ n, n0 ≤ n →
      ∑ k ∈ Finset.range (n + 1), fA x y k
        = (∑ k ∈ Finset.range (n0 + 1), fA x y k) - fA x y n0 / 2 + fA x y n / 2
          + (FA x y n - FA x y n0) + ∑ k ∈ Finset.Ico n0 n, eA x y k := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top hmn]
    unfold eA
    push_cast
    ring

theorem sumE_bounds (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (n0 n : ℕ) (hn : n0 ≤ n) :
    0 ≤ ∑ k ∈ Finset.Ico n0 n, eA x y k ∧
      ∑ k ∈ Finset.Ico n0 n, eA x y k ≤ (gA x y n - gA x y n0) / 4 := by
  constructor
  · exact Finset.sum_nonneg fun k _ => (eA_bounds x y hx hy k).1
  · have hle : ∑ k ∈ Finset.Ico n0 n, eA x y k
        ≤ ∑ k ∈ Finset.Ico n0 n, (gA x y (((k + 1 : ℕ) : ℝ)) - gA x y k) / 4 := by
      apply Finset.sum_le_sum
      intro k _
      have := (eA_bounds x y hx hy k).2
      push_cast
      exact this
    have htel : ∑ k ∈ Finset.Ico n0 n, (gA x y (((k + 1 : ℕ) : ℝ)) - gA x y k) / 4
        = (gA x y n - gA x y n0) / 4 := by
      rw [← Finset.sum_div]
      rw [Finset.sum_Ico_sub (fun k : ℕ => gA x y (k:ℝ)) hn]
    linarith

/-- **Finite sandwich.**  For `n >= n0`, with `H n = y log n - FA n - fA n / 2` and the constant
    `C0 = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k`:
        H n + C0 + gA n0 / 4 <= imLnVal x y n <= H n + C0. -/
theorem imLnVal_sandwich (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (n0 n : ℕ) (hn : n0 ≤ n) :
    (y * Real.log n - FA x y n - fA x y n / 2)
        + (FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k)
        + gA x y n0 / 4 ≤ imLnVal x y n ∧
      imLnVal x y n ≤ (y * Real.log n - FA x y n - fA x y n / 2)
        + (FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k) := by
  have hsum := sum_split x y n0 n hn
  have hE := sumE_bounds x y hx hy n0 n hn
  have hgn := gA_nonpos x y (n:ℝ) hy
  have himl : imLnVal x y n = y * Real.log n - ∑ k ∈ Finset.range (n + 1), fA x y k := rfl
  rw [himl, hsum]
  constructor <;> linarith [hE.1, hE.2]

/-! ## 4.  The limit of `H n` and the Stirling bracket for `Lam`. -/





/-! ## 5.  The Riemann-Siegel phase: the `n0 = 0`, `x = 1/4`, `y = t/2` specialisation. -/









/-! ## 6.  The numeric instance at `t = 280000` (the top of the h280000 ladder).

All constants below are short decimals chosen by an untrusted script; every inequality between
them and the exact series values is re-checked by `norm_num`/`linarith` in the kernel.  The log
brackets use Mathlib's `Real.abs_log_sub_add_sum_range_le` (Taylor series of `log (1 - x)` with the
geometric remainder `|x|^(n+1)/(1-|x|)`), the pi bracket is Mathlib's `pi_gt_d20`/`pi_lt_d20`. -/



















end RSDesignTheta


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




theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (n0 : ℕ) (Λ : ℝ)
    (hΛ : Tendsto (imLnVal x y) atTop (𝓝 Λ)) :
    (FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k - y)
        - y / (4 * ((x + n0) ^ 2 + y ^ 2)) ≤ Λ ∧
      Λ ≤ FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k - y := by
  set C0 : ℝ := FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k with hC0
  have hH := tendsto_H x y hx hy
  have hup : Tendsto (fun n : ℕ => (y * Real.log n - FA x y n - fA x y n / 2) + C0) atTop
      (𝓝 (-y + C0)) := hH.add_const C0
  have hlo : Tendsto (fun n : ℕ => (y * Real.log n - FA x y n - fA x y n / 2) + C0
      + gA x y n0 / 4) atTop (𝓝 (-y + C0 + gA x y n0 / 4)) := hup.add_const _
  have hgA : gA x y n0 / 4 = -(y / (4 * ((x + n0) ^ 2 + y ^ 2))) := by
    unfold gA
    have : 0 < (x + (n0:ℝ)) ^ 2 + y ^ 2 := by
      have : 0 < x + (n0:ℝ) := by positivity
      positivity
    field_simp
  constructor
  · have h := le_of_tendsto_of_tendsto hlo hΛ (by
      filter_upwards [eventually_ge_atTop n0] with n hn
      exact (imLnVal_sandwich x y hx hy n0 n hn).1)
    rw [hgA] at h
    linarith
  · have h := le_of_tendsto_of_tendsto hΛ hup (by
      filter_upwards [eventually_ge_atTop n0] with n hn
      exact (imLnVal_sandwich x y hx hy n0 n hn).2)
    linarith
