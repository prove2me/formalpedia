-- Prove2me | solution 1 for RSSeam.rs_Z_C0_seam
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:42:04.957402+00:00
-- url     : https://prove2.me/submissions/f804bdc7-7d15-4dce-942f-96f4654a3e41

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Theorems.Thm_RSDesignTheta_theta_sub_thetaMain
import Theorems.Thm_RSInt_completed_re_eq_rs_cos
import Theorems.Thm_RSSeam_rs_remainder_C0_alpha_seam
import Theorems.Thm_ThetaConverge_convergence_obligation
import Theorems.Thm_ZeroSignDecomp_gamma_r_polar_t
namespace RSInt
end RSInt
/-  RS_B3Bound.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 3: the
    analytic estimates and THE B3 HEADLINE.  Mathlib-only (imports `RS_B3`).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase phi with
      |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4),
      where rsRem t is the EXACT Riemann-Siegel remainder of B2 and Psi = Gabcke's C0.  With B2's
      `completed_re_eq_rs_cos` this is the classical
          Z(t) = 2 sum_{n<=N} n^(-1/2) cos(theta - t log n) + (-1)^(N-1) (t/2pi)^(-1/4) C0(p) + R,
          |R| <= 2 t^(-3/4)   (t >= 10000),
      with an explicit, kernel-checked constant (Gabcke's sharper 0.127 is NOT claimed).
      `rs_remainder_C0_alpha` is the same bound in the saddle variable a = sqrt(t/2pi):
      |...| <= (2/5) a^(-3/2).

    ## The estimates behind it

      * `integral_sq_mul_exp_neg_mul_sq` : int v^2 e^{-b v^2} dv = sqrt(pi/b) / (2b).
      * `norm_rsD_ge_two_pi_im` : |rsD z| >= 2 pi |Im z|;  `two_le_norm_rsD_midline` : |rsD| >= 2 on
        the line Re x - Im x = 1/2 (sin^2 + sinh^2 >= 1).
      * `norm_rsPhi_sub_one_le` : for |w| <= a/2 the saddle-point amplitude satisfies
            |rsPhi a w - 1| <= e e^e,   e = |w|/(2a) + |w|^2/(2a^2) + (4 pi/3)|w|^3/a
        (complex Taylor bounds for log(1+u), Mathlib `norm_log_sub_logTaylor_le`).
      * `saddle_arg_le` : along the steepest-descent line, 2 pi a^2 arg(1 + v(1+i)/a) - 2 pi (a+v) v
        <= -pi v^2 for every real v (a derivative-sign argument: the saddle is a global maximum);
        `norm_gauss_rsPhi_le` : |e^{2 pi i w^2} rsPhi a w| <= 2 e^{-pi v^2} on w = v(1+i).
      * `rsJ_eq_mid`, `norm_rsJ_le` : the tau = 2 Mordell integral moves (strip Cauchy, no pole) to the
        midline through 1/2 - p, where |rsJ p| <= 4 uniformly in p ∈ (0,1).
      * `norm_E1_integrand_near` (|v| <= a/9) / `norm_E1_integrand_far` (|v| >= a/9), `norm_rsE1_le`,
        `E1_const_le` : |rsE1 a p| <= (9/50)/a for a >= 39.

    conjecture1_proved = False.  An explicit remainder inequality for the Riemann-Siegel formula at
    finite height; nothing here bears on the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. The second Gaussian moment -/





/-! ## 2. Lower bound for the denominator -/



/-! ## 3. The amplitude near the saddle point -/







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/











/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

















/-! ## 7. The explicit C0 remainder bound -/





theorem rsAlpha_rpow_neg_half {t : ℝ} (ht : 0 ≤ t) :
    (rsAlpha t) ^ (-(1 / 2 : ℝ)) = (t / (2 * π)) ^ (-(1 / 4 : ℝ)) := by
  unfold rsAlpha
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

theorem rsAlpha_rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    (rsAlpha t) ^ (-(3 / 2 : ℝ)) = (2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ)) := by
  unfold rsAlpha
  have e : (1 / 2 : ℝ) * (-(3 / 2)) = -(3 / 4) := by norm_num
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), e, Real.div_rpow ht.le (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * π), div_inv_eq_mul]
  ring

theorem two_pi_rpow_three_quarters_le : (2 * π) ^ (3 / 4 : ℝ) ≤ 4 := by
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hπ : 2 * π ≤ 63 / 10 := by linarith [Real.pi_lt_d2]
  have e : (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast]
  calc (2 * π) ^ 3 ≤ (63 / 10) ^ 3 := pow_le_pow_left₀ (by positivity) hπ 3
    _ ≤ 4 ^ 4 := by norm_num



end RSInt

end

/-  RSSeam_B3Bound.lean -- lane SEAM: the C0-corrected Riemann-Siegel remainder bound with a LOWER
    starting height, t >= 509 (saddle variable a = sqrt(t/2pi) >= 9) instead of t >= 10000 (a >= 39).
    Imports `RS_B3Bound` read-only and reuses its lemmas; nothing in lane RS is edited.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0_alpha_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase
      phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (13/20) a^(-3/2).
      `rs_remainder_C0_seam` : the same in t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4).

    ## What changed against `RS_B3Bound` (the error budget re-run at a >= 9)

      * near/far split of the error integral at |v| = a/3 (was a/9); near the saddle the amplitude
        bound |rsPhi - 1| <= e e^e still applies because |w| = sqrt 2 |v| <= a/2;
      * near: e <= |w| (13/25 + 17/4 |w|^2)/a and e <= 27/5 v^2 + 1/600, so the integrand is
        <= e^{1/600}/(pi a) (13/25 + 17/2 v^2) e^{-7 v^2};
      * far: |integrand| <= 5 e^{-pi a^2/18} e^{-pi v^2/2}, and e^{-x} <= 8!/x^8 at x >= 14;
      * |rsE1 a p| <= (49/200 + 1/200)/a = (1/4)/a for a >= 9 (was (9/50)/a for a >= 39);
      * |rsJ p| <= 4 (unchanged, `RSInt.norm_rsJ_le`); phase term 8|delta| <= 4/(pi a^2) <= (3/20)/a;
      * budget 2 (1/4) + 3/20 = 13/20 in the a-form; (2 pi)^(3/4) <= 4 gives 13/5 in t.

    Untrusted numerics (scratchpad/seam/remainder.py): the true C0-corrected remainder is
    <= 0.121 t^(-3/4) on samples in [200, 10100]; so 13/5 is honest with a ~20x margin.

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSSeam

open RSInt









/-! ## The explicit C0 remainder bound from t >= 509 -/





/-- **SEAM HEADLINE: the explicit C0-corrected Riemann-Siegel remainder bound from t >= 509.**
    For `t >= 509`, `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0`, and any phase `phi` with
    `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4). -/
theorem rs_remainder_C0_seam {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := rs_remainder_C0_alpha_seam ht hp hcos hφ
  rw [rsAlpha_rpow_neg_half ht0.le, rsAlpha_rpow_neg_three_halves ht0] at h
  have ht34 := Real.rpow_pos_of_pos ht0 (-(3 / 4 : ℝ))
  calc _ ≤ 13 / 20 * ((2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := h
    _ ≤ 13 / 20 * (4 * t ^ (-(3 / 4 : ℝ))) := by gcongr; exact two_pi_rpow_three_quarters_le
    _ = 13 / 5 * t ^ (-(3 / 4 : ℝ)) := by ring

end RSSeam

end

/-  RS_Bridge.lean -- lane RS, brick B3 part 4: the Riemann-Siegel formula for Hardy's Z with the
    C0 term and an explicit remainder, HYPOTHESIS-FREE on the phase (imports `RS_B3Bound`, the
    island's `RSTheta` Stirling bracket and `ZeroSignDecomp_t14` polar form; all read-only).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_Z_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= 2 t^(-3/4),
      N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p).

    The phase phi = Lam - (t/2) log pi is the island's branch-correct Riemann-Siegel theta
    (`ThetaConverge.convergence_obligation` + `ZeroSignDecomp.gamma_r_polar_t`), and the bound
    |phi - thetaMain t| <= 1/t is `RSDesignTheta.theta_sub_thetaMain`.  The quotient on the left is
    Hardy's Z(t) (Re Lambda(1/2+it) = M Z(t), M = |Gammaℝ(1/2+it)| > 0): its sign is the sign of the
    island's `gLine t`, so a sign certificate for gLine at height t >= 10000 now needs only the
    finite main sum, one Psi value and the margin 2 t^(-3/4).

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/




open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

theorem rsThetaMain_eq_thetaMain (t : ℝ) : rsThetaMain t = ZeroFreeBridge.thetaMain t := rfl



end RSInt

end

/-  RSSeam_Bridge.lean -- lane SEAM: the Riemann-Siegel formula for Hardy's Z with the C0 term and an
    explicit remainder from t >= 509, phase discharged HYPOTHESIS-FREE exactly as in `RS_Bridge`
    (imports `RSSeam_B3Bound`, `RS_Bridge`, the island's `RSTheta` and `ZeroSignDecomp_t14`;
    all read-only).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_Z_C0_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (13/5) t^(-3/4),
      N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p).

    This is `RSInt.rs_Z_C0` with the range lowered from t >= 10000 to t >= 509 (constant 2 -> 13/5),
    so the Riemann-Siegel range now overlaps the Euler-Maclaurin kernel ladder (which reaches 1000 on
    this branch and 8000 via `AND.ladder_h8000_kernel`).

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/



open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSSeam
end RSSeam
open RSSeam

open RSInt


theorem solution {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hGne : Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    linarith
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    ThetaConverge.convergence_obligation (1 / 4) (t / 2) (by norm_num) hGne
  obtain ⟨M, hM, hpolar⟩ := ZeroSignDecomp.gamma_r_polar_t t ht0.ne' Λ hbranch
  have hθ := RSDesignTheta.theta_sub_thetaMain t ht0 Λ hΛtend
  set φ : ℝ := Λ - t / 2 * Real.log Real.pi with hφ
  have hφb : |φ - rsThetaMain t| ≤ 1 / t := by
    rw [rsThetaMain_eq_thetaMain]; exact hθ
  refine ⟨M, φ, hM, hpolar, hφb, ?_⟩
  have hN : ((rsNn t : ℕ) : ℝ) < (rsNn t : ℝ) + 1 / 2 := by linarith
  have hN' : (rsNn t : ℝ) + 1 / 2 < (rsNn t : ℝ) + 1 := by linarith
  have hre := completed_re_eq_rs_cos t (rsNn t) hN hN' hpolar
  have hrem : -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))) =
      rsRem t := rfl
  rw [hrem] at hre
  rw [hre]
  have hC0 := rs_remainder_C0_seam ht hp hcos hφb
  have e : 2 * M * ((∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.cos (φ - t * Real.log n)) + (cexp (I * φ) * rsRem t).re) / M -
      (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)) =
      2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t) := by
    field_simp
    ring
  rw [e]
  exact hC0
