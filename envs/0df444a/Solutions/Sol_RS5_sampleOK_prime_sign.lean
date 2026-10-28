-- Prove2me | solution 1 for RS5.sampleOK_prime_sign
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:46:25.259305+00:00
-- url     : https://prove2.me/submissions/7a2afdc7-d090-4259-ab2e-404439a20ed3

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS5_Z
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_BandSharp
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_RS5_check5_sound
import Theorems.Thm_RS5_tpow_le_margin
import Theorems.Thm_RSInt_rs_Z_of_remainder
import Theorems.Thm_RSInt_rs_remainder_C0_alpha_prime
namespace ArbEcon
end ArbEcon
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv
namespace RS4
end RS4
namespace RS4.Cert
end RS4.Cert
namespace RSInt
end RSInt
/-  RS4_Sound.lean -- lane B4: SOUNDNESS of the Riemann-Siegel main-term checker `RS4.check`.

    ## The headline

      `RS4.check_sound` : for an evaluator configuration `c` valid at height `t`
      (`ArbEcon.Valid c t K`, i.e. `t = tn / 2^tq` and the pi / Horner / log-kernel facts) and any
      certificate `z`, if the KERNEL accepts (`check c z = true`) then
        * `10000 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and
        * for EVERY phase `phi` with `|phi - rsThetaMain t| <= 1/t`,
              z.zlo / 2^(2P) <= Zmain t phi <= z.zhi / 2^(2P),
          where `Zmain t phi = 2 sum_{n <= N} n^(-1/2) cos(phi - t log n)
                                + (-1)^(N+1) (t/2pi)^(-1/4) rsPsi (rsFrac t)`
          is VERBATIM the main term of `RSInt.rs_Z_C0`.

    The hypotheses of `rs_Z_C0` (`t >= 10000`, `0 < p`, `cos 2 pi p ≠ 0`) are OUTPUTS of the checker,
    so `RS4_Z` combines the two into a hypothesis-free enclosure of Hardy's Z.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/




open Real Finset
open ArbEcon DIntvProd

namespace RS4

noncomputable section



/-! ## 0. small real facts -/

















/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem oneR (hv : Valid c t K) : (c.one : ℝ) = 2 ^ c.P := by
  rw [hv.one_eq]; push_cast; ring





















































/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/







/-! ## 3. the phase ball -/











/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/









/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/















end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/







/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/



/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}









end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/



end

end RS4


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

/-  RS5_Z.lean -- lane B5: the t >= 509 checker `RS5.check5` glued to the SEAM bound
    `RSSeam.rs_Z_C0_seam` (remainder (13/5) t^(-3/4)), and certified signs of one dyadic sample.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure` : `Valid c t K`, `check5 c z = true` give `M > 0`, `phi` with
            Gammaℝ(1/2+it) = M e^{i phi},  |phi - thetaMain t| <= 1/t,
            zlo/2^(2P) - (13/5) t^(-3/4) <= Re completedRiemannZeta(1/2+it) / M
                                         <= zhi/2^(2P) + (13/5) t^(-3/4)
        (the EXACT t-dependent margin of the seam bound; valid from t >= 509).
      * `tpow_le_margin` : `MarginOK c E` (an integer inequality) gives `t^(-3/4) <= E / 2^P`.
      * `rs5_Z_enclosure_E` : the same enclosure with the rational margin `(13/5) E / 2^P`.
      * `rs5_sign_pos` / `rs5_sign_neg` : a box clearing `(13/5) E / 2^P` on one side pins the SIGN of
        `Re completedRiemannZeta(1/2+it)` (= `XiLineZeros.gLine t`).
      * `sampleOK_sign` : a certified `Sample` (`sampleOK s = true`) has the claimed sign of `gLine`
        at `s.t = tn / 2^tq`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/





open Complex
open scoped Real

namespace RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section















/-! ## one sample -/



theorem Sample.valid (s : Sample) : Valid s.cfg s.t 9 := ArbEcon.OrderK.valid64 s.tn s.tq _ rfl



end

end RS5


/-  RS_B3Sharp.lean -- lane RS, brick B3 SHARPENED (RSC0 Phase 2): the same C0-corrected
    Riemann-Siegel remainder as `RS_B3Bound` / `RSSeam_B3Bound`, with smaller kernel-checked constants.
    New theorems only; imports `RSSeam_B3Bound` (hence `RS_B3Bound`) read-only and edits nothing.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_remainder_C0_alpha'` : for t >= 4250 (a = sqrt(t/2pi) >= 26), 0 < p = rsFrac t,
      cos(2 pi p) ≠ 0, and every phase phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2);
      `RSInt.rs_remainder_C0'` : the same in t, <= (3/5) t^(-3/4).
      `RSSeam.rs_remainder_C0_alpha_seam'` : for t >= 509, <= (21/100) a^(-3/2);
      `RSSeam.rs_remainder_C0_seam'` : the same in t, <= (21/25) t^(-3/4).
      The old statements (2/5 and 2 at t >= 10000; 13/20 and 13/5 at t >= 509) are re-derived from
      the new ones as `*_of_sharp` corollaries at the end of the file.

    ## What is sharper than `RS_B3Bound` (same architecture, elementary steps)

      * the saddle exponent E is split as E = E1 + E2 with E1 = -2 pi i w^3/(3a) - w/(2a) EXACT and
        |E2| <= pi |w|^4/a^2 + |w|^2/(2a^2) (Mathlib's log-Taylor remainders of orders 4 and 2), and
        |e^E - 1| <= |E| + |E|^2 e^{|E|} (`norm_rsPhi_sub_one_le'`);
      * on the steepest-descent line |E1| = (sqrt2/2)|v| |1 - 8 pi v^2/3| / a EXACTLY (`rsEone_line`):
        the linear and cubic terms have OPPOSITE signs, and |1 - x| <= 41/40 - (5/4)x + (5/8)x^2;
        the main term then integrates against the FULL Gaussian e^{-4 pi v^2} to (49/120)/(2 pi a);
      * only the second-order remainder pays for e^{|E|}, with e^{-(4 pi - 37/10) v^2};
      * absolute Gaussian moments int |v|^j e^{-b v^2} = b^{-(j+1)/2} Gamma((j+1)/2) (`gaussMom_eq`);
      * one near-zone lemma (|v| <= a/3) for every a >= a0 >= 9, the far zone reused verbatim from
        `RSSeam.norm_E1_integrand_far`;
      * |rsJ p| <= 4/5 by completing the square on the midline (was 4) (`norm_rsJ_le'`).
      Budget: |rsE1| <= (7/100)/a (a >= 26) and (9/100)/a (a >= 9); phase 4/(5 pi a^2) <= (1/100)/a
      resp. (3/100)/a; 2 (7/100) + 1/100 = 3/20 and 2 (9/100) + 3/100 = 21/100; (2 pi)^(3/4) <= 4.

    The numeric lemmas bound a|rsE1| by 0.0689 (a >= 26) and 0.0821 (a >= 9).  Untrusted design
    numerics (closed forms 0.0688 and 0.0770): ~/rh-team/rsc0/out/phase2/lean_numerics.py.

    Not yet `lean_lib`s (lakefile.toml untouched): compile with `lake env lean`; a landing PR adds
    append-only `[[lean_lib]]` entries for RS_B3Sharp and RS_BridgeSharp (and RS_AxiomGuardSharp).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Absolute Gaussian moments -/





































/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/





































/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/





























/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/





/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/





/-- **HEADLINE (sharpened): the explicit C0-corrected Riemann-Siegel remainder bound, t >= 4250.**
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (3/5) t^(-3/4). -/
theorem rs_remainder_C0' {t : ℝ} (ht : 4250 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      3 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := _root_.RSInt.rs_remainder_C0_alpha_prime ht hp hcos hφ
  rw [rsAlpha_rpow_neg_half ht0.le, rsAlpha_rpow_neg_three_halves ht0] at h
  have ht34 := Real.rpow_pos_of_pos ht0 (-(3 / 4 : ℝ))
  calc _ ≤ 3 / 20 * ((2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := h
    _ ≤ 3 / 20 * (4 * t ^ (-(3 / 4 : ℝ))) := by gcongr; exact two_pi_rpow_three_quarters_le
    _ = 3 / 5 * t ^ (-(3 / 4 : ℝ)) := by ring

/-! ## 8. The old headlines re-derived from the sharpened ones -/





end RSInt

namespace RSSeam

open RSInt

/-! ## 9. The seam, sharpened: t >= 509 (a >= 9) -/









end RSSeam

end

/-  RS_BridgeSharp.lean -- lane RS, brick B3 part 4 SHARPENED (RSC0 Phase 2): the Riemann-Siegel
    formula for Hardy's Z with the C0 term and the SHARPENED explicit remainders of `RS_B3Sharp`,
    phase discharged hypothesis-free exactly as in `RS_Bridge` / `RSSeam_Bridge` (imports
    `RS_B3Sharp`, `RS_Bridge`; all read-only, nothing existing is edited).

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_Z_C0'` : for t >= 4250, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (3/5) t^(-3/4).
      `RSSeam.rs_Z_C0_seam'` : the same for t >= 509 with (21/25) t^(-3/4).
      Same statement shape as `RSInt.rs_Z_C0` (2 t^(-3/4), t >= 10000) and `RSSeam.rs_Z_C0_seam`
      ((13/5) t^(-3/4), t >= 509); those two statements are re-derived here from the sharpened
      remainders as `RSInt.rs_Z_C0_of_sharp` and `RSSeam.rs_Z_C0_seam_of_sharp`.

    `rs_Z_of_remainder` is the proof of `RSInt.rs_Z_C0` with the remainder constant abstracted:
    any bound C on the C0-corrected remainder, valid for every phase within 1/t of thetaMain, is a
    bound on the Z formula with the island's branch-correct theta.

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/



open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt



/-- **The Riemann-Siegel formula with the C0 term, sharpened remainder, t >= 4250.**  Same shape
    as `rs_Z_C0`; remainder `(3/5) t^(-3/4)` instead of `2 t^(-3/4)`, from t >= 4250 instead of
    t >= 10000. -/
theorem rs_Z_C0' {t : ℝ} (ht : 4250 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        3 / 5 * t ^ (-(3 / 4 : ℝ)) :=
  rs_Z_of_remainder (by linarith) fun _ hφ => rs_remainder_C0' ht hp hcos hφ



end RSInt

namespace RSSeam

open RSInt





end RSSeam

end

/-  RS5_ZSharp.lean -- lane B5, RSC0 Phase 3: the t >= 509 checker `RS5.check5` glued to the SHARPENED
    bound `RSInt.rs_Z_C0'` (remainder (3/5) t^(-3/4), t >= 4250; RS_BridgeSharp), and certified signs of
    one dyadic sample under `RS5.sampleOK'`.  Variants BESIDE `RS5_Z` (imported read-only).

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure'` : `Valid c t K`, `check5 c z = true`, `4250 <= t` give the enclosure of
        `Re completedRiemannZeta(1/2+it) / M` by the box widened by `(3/5) t^(-3/4)`;
      * `rs5_Z_enclosure_E'` : the same with the rational margin `(3/5) E / 2^P` (`MarginOK`);
      * `posOK'_real` / `negOK'_real` : the integer tests `PosOK'` / `NegOK'` cast to reals;
      * `rs5_sign_pos'` / `rs5_sign_neg'` and `sampleOK'_sign` : a sample accepted by `sampleOK'` has the
        claimed sign of `gLine` at `s.t`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/




open Complex
open scoped Real

namespace RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section

/-- **Enclosure from the sharpened bound (t >= 4250), exact margin `(3/5) t^(-3/4)`.** -/
theorem rs5_Z_enclosure' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) (ht4 : 4250 ≤ t) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 3 / 5 * t ^ (-(3 / 4 : ℝ)) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 3 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨_, _, hp, hcos, hZ⟩ := check5_sound hv z h
  obtain ⟨M, φ, hM, hpol, hφ, hb⟩ := RSInt.rs_Z_C0' ht4 hp hcos
  refine ⟨M, φ, hM, hpol, hφ, ?_⟩
  have hz := hZ φ hφ
  unfold Zmain at hz
  rw [abs_le] at hb
  constructor <;> linarith [hz.1, hz.2, hb.1, hb.2]

/-- **Enclosure with the rational margin `(3/5) E / 2^P`.** -/
theorem rs5_Z_enclosure_E' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (ht4 : 4250 ≤ t) (hm : MarginOK c E) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 3 / 5 * ((E : ℝ) / 2 ^ c.P) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 3 / 5 * ((E : ℝ) / 2 ^ c.P) := by
  obtain ⟨M, φ, hM, hpol, hφ, h1, h2⟩ := rs5_Z_enclosure' hv z h ht4
  have hmr := tpow_le_margin hv (by linarith) hm
  exact ⟨M, φ, hM, hpol, hφ, by linarith, by linarith⟩

theorem posOK'_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hp : PosOK' c z E) : 3 / 5 * ((E : ℝ) / 2 ^ c.P) < (z.zlo : ℝ) / 2 ^ (2 * c.P) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((3 * (E : ℤ) * (c.one : ℤ) : ℤ) : ℝ) < ((5 * z.zlo : ℤ) : ℝ) := by exact_mod_cast hp
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : (z.zlo : ℝ) / 2 ^ (2 * c.P) - 3 / 5 * ((E : ℝ) / 2 ^ c.P)
      = (5 * z.zlo - 3 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (5 * (z.zlo : ℝ) - 3 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

theorem negOK'_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hn : NegOK' c z E) : (z.zhi : ℝ) / 2 ^ (2 * c.P) < -(3 / 5 * ((E : ℝ) / 2 ^ c.P)) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((5 * z.zhi : ℤ) : ℝ) < ((-(3 * (E : ℤ) * (c.one : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : -(3 / 5 * ((E : ℝ) / 2 ^ c.P)) - (z.zhi : ℝ) / 2 ^ (2 * c.P)
      = (-(3 * E * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (-(3 * (E : ℝ) * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- A certified box above `(3/5) E / 2^P` (t >= 4250) gives `Re completedRiemannZeta(1/2+it) > 0`. -/
theorem rs5_sign_pos' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (ht4 : 4250 ≤ t) (hm : MarginOK c E) (hpos : PosOK' c z E) :
    0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re := by
  obtain ⟨M, _, hM, _, _, h1, _⟩ := rs5_Z_enclosure_E' hv z h ht4 hm
  have := posOK'_real hv hpos
  have : 0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M := by linarith
  exact (div_pos_iff_of_pos_right hM).mp this

/-- A certified box below `-(3/5) E / 2^P` (t >= 4250) gives `Re completedRiemannZeta(1/2+it) < 0`. -/
theorem rs5_sign_neg' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (ht4 : 4250 ≤ t) (hm : MarginOK c E) (hneg : NegOK' c z E) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re < 0 := by
  obtain ⟨M, _, hM, _, _, _, h2⟩ := rs5_Z_enclosure_E' hv z h ht4 hm
  have := negOK'_real hv hneg
  have : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M < 0 := by linarith
  by_contra hc
  have := div_nonneg (not_lt.mp hc) hM.le
  linarith

/-- The decided height test is the real hypothesis `4250 <= s.t`. -/
theorem heightOK_real {s : Sample} (h : HeightOK s) : (4250 : ℝ) ≤ s.t := by
  unfold HeightOK at h
  unfold Sample.t
  have h' : ((4250 * 2 ^ s.tq : ℕ) : ℝ) ≤ ((s.tn : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  rw [le_div_iff₀ (by positivity)]
  exact h'



end

end RS5


/-  RS5_ZSharp.lean -- lane B5, RSC0 Phase 3: the t >= 509 checker `RS5.check5` glued to the SHARPENED
    bound `RSInt.rs_Z_C0'` (remainder (3/5) t^(-3/4), t >= 4250; RS_BridgeSharp), and certified signs of
    one dyadic sample under `RS5.sampleOK'`.  Variants BESIDE `RS5_Z` (imported read-only).

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure'` : `Valid c t K`, `check5 c z = true`, `4250 <= t` give the enclosure of
        `Re completedRiemannZeta(1/2+it) / M` by the box widened by `(3/5) t^(-3/4)`;
      * `rs5_Z_enclosure_E'` : the same with the rational margin `(3/5) E / 2^P` (`MarginOK`);
      * `posOK'_real` / `negOK'_real` : the integer tests `PosOK'` / `NegOK'` cast to reals;
      * `rs5_sign_pos'` / `rs5_sign_neg'` and `sampleOK'_sign` : a sample accepted by `sampleOK'` has the
        claimed sign of `gLine` at `s.t`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/




open Complex
open scoped Real

section
namespace RS5
end RS5
open RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section
















theorem solution {s : Sample} (h : sampleOK' s = true) :
    (s.pos = true → 0 < XiLineZeros.gLine s.t) ∧ (s.pos = false → XiLineZeros.gLine s.t < 0) := by
  unfold sampleOK' at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hH, hc⟩, hm⟩, hs⟩ := h
  have ht4 := heightOK_real hH
  constructor
  · intro hp
    rw [hp, if_pos rfl, decide_eq_true_eq] at hs
    exact rs5_sign_pos' s.valid s.z hc ht4 hm hs
  · intro hp
    rw [hp] at hs
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hs
    exact rs5_sign_neg' s.valid s.z hc ht4 hm hs
