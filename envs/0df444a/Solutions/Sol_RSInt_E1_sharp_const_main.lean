-- Prove2me | solution 1 for RSInt.E1_sharp_const_main
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:49:17.226757+00:00
-- url     : https://prove2.me/submissions/3022e453-d144-4714-bae9-34aa6cb3b30a

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
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



theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]













/-! ## 7. The explicit C0 remainder bound -/













end RSInt

end

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





theorem gaussMom_eq {b : ℝ} (hb : 0 < b) (j : ℕ) :
    gaussMom b j = b ^ (-((j : ℝ) + 1) / 2) * Real.Gamma (((j : ℝ) + 1) / 2) := by
  unfold gaussMom
  have hj : (-1 : ℝ) < j := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h1 : (fun v : ℝ => |v| ^ j * Real.exp (-b * v ^ 2)) =
      fun v => (fun r : ℝ => r ^ j * Real.exp (-b * r ^ 2)) |v| := by
    ext v; simp only [sq_abs]
  rw [h1, integral_comp_abs (f := fun r : ℝ => r ^ j * Real.exp (-b * r ^ 2))]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (j : ℝ)) (b := b) (by norm_num) hj hb
  have h3 : ∫ x in Ioi (0 : ℝ), (fun r : ℝ => r ^ j * Real.exp (-b * r ^ 2)) x =
      ∫ x in Ioi (0 : ℝ), x ^ (j : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [Real.rpow_natCast, Real.rpow_two]
  rw [h3, h2]
  ring

theorem gaussMom_odd {b : ℝ} (hb : 0 < b) (m : ℕ) :
    gaussMom b (2 * m + 1) = (m.factorial : ℝ) / b ^ (m + 1) := by
  rw [gaussMom_eq hb]
  have e1 : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by push_cast; ring
  have e2 : -(((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = -(((m + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [e1, e2, Real.Gamma_nat_eq_factorial, Real.rpow_neg hb.le, Real.rpow_natCast]
  field_simp

theorem gaussMom_even {b : ℝ} (hb : 0 < b) (m : ℕ) :
    gaussMom b (2 * m) = Real.Gamma ((m : ℝ) + 1 / 2) / (b ^ m * Real.sqrt b) := by
  rw [gaussMom_eq hb]
  have e1 : (((2 * m : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
  have e2 : -(((2 * m : ℕ) : ℝ) + 1) / 2 = -((m : ℝ) + 1 / 2) := by push_cast; ring
  rw [e1, e2, Real.rpow_neg hb.le, Real.rpow_add hb, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  field_simp

theorem Gamma_three_halves' : Real.Gamma (1 + 1 / 2) = Real.sqrt π / 2 := by
  rw [show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

theorem Gamma_five_halves' : Real.Gamma (2 + 1 / 2) = 3 * Real.sqrt π / 4 := by
  rw [show (2 : ℝ) + 1 / 2 = (1 + 1 / 2) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_three_halves']
  ring

theorem Gamma_seven_halves' : Real.Gamma (3 + 1 / 2) = 15 * Real.sqrt π / 8 := by
  rw [show (3 : ℝ) + 1 / 2 = (2 + 1 / 2) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_five_halves']
  ring

theorem gaussMom_0 (b : ℝ) : gaussMom b 0 = Real.sqrt (π / b) := by
  unfold gaussMom
  simp only [pow_zero, one_mul]
  exact integral_gaussian b

theorem gaussMom_1 {b : ℝ} (hb : 0 < b) : gaussMom b 1 = 1 / b := by
  have := gaussMom_odd hb 0
  simpa using this

theorem gaussMom_2 {b : ℝ} (hb : 0 < b) : gaussMom b 2 = Real.sqrt (π / b) / (2 * b) := by
  have h := gaussMom_even hb 1
  rw [show 2 * 1 = 2 by rfl] at h
  rw [h, Real.sqrt_div' π hb.le]
  have hG : Real.Gamma (((1 : ℕ) : ℝ) + 1 / 2) = Real.sqrt π / 2 := by
    rw [Nat.cast_one]; exact Gamma_three_halves'
  rw [hG, pow_one]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp

theorem gaussMom_3 {b : ℝ} (hb : 0 < b) : gaussMom b 3 = 1 / b ^ 2 := by
  have := gaussMom_odd hb 1
  simpa using this

theorem gaussMom_4 {b : ℝ} (hb : 0 < b) : gaussMom b 4 = 3 * Real.sqrt (π / b) / (4 * b ^ 2) := by
  have h := gaussMom_even hb 2
  rw [show 2 * 2 = 4 by rfl] at h
  rw [h, Real.sqrt_div' π hb.le]
  have hG : Real.Gamma (((2 : ℕ) : ℝ) + 1 / 2) = 3 * Real.sqrt π / 4 := by
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]; exact Gamma_five_halves'
  rw [hG]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp

theorem gaussMom_5 {b : ℝ} (hb : 0 < b) : gaussMom b 5 = 2 / b ^ 3 := by
  have := gaussMom_odd hb 2
  simpa [Nat.factorial] using this

theorem gaussMom_6 {b : ℝ} (hb : 0 < b) :
    gaussMom b 6 = 15 * Real.sqrt (π / b) / (8 * b ^ 3) := by
  have h := gaussMom_even hb 3
  rw [show 2 * 3 = 6 by rfl] at h
  rw [h, Real.sqrt_div' π hb.le]
  have hG : Real.Gamma (((3 : ℕ) : ℝ) + 1 / 2) = 15 * Real.sqrt π / 8 := by
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]; exact Gamma_seven_halves'
  rw [hG]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp

theorem gaussMom_7 {b : ℝ} (hb : 0 < b) : gaussMom b 7 = 6 / b ^ 4 := by
  have := gaussMom_odd hb 3
  simpa [Nat.factorial] using this





/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/



theorem sqrt_two_le_141422 : Real.sqrt 2 ≤ 141422 / 100000 := by
  calc Real.sqrt 2 ≤ Real.sqrt ((141422 / 100000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 141422 / 100000 := Real.sqrt_sq (by norm_num)

































/-! ## 4. The error integral, sharpened -/

theorem sqrt_pi_div_four_pi : Real.sqrt (π / (4 * π)) = 1 / 2 := by
  rw [show π / (4 * π) = (1 / 2) ^ 2 by rw [div_eq_iff (by positivity)]; ring]
  exact Real.sqrt_sq (by norm_num)

theorem sum_cMain_gauss : ∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j = 49 / 120 := by
  have hb : (0 : ℝ) < 4 * π := by positivity
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cMain]
  norm_num
  rw [gaussMom_0, gaussMom_2 hb, gaussMom_4 hb, sqrt_pi_div_four_pi]
  field_simp
  ring

theorem sum_cEtwo_gauss : ∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j = 1 / (2 * π) := by
  have hb : (0 : ℝ) < 4 * π := by positivity
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cEtwo]
  norm_num
  rw [gaussMom_1 hb, gaussMom_3 hb]
  field_simp
  ring

theorem sum_cS_gauss (a0 : ℝ) {b : ℝ} (hb : 0 < b) :
    ∑ j ∈ Finset.range 8, cS a0 j * gaussMom b j =
      1 / 2 * (1 / b) + Real.sqrt 2 / a0 * (Real.sqrt (π / b) / (2 * b)) +
        (8 * π / 3 + 1 / a0 ^ 2) * (1 / b ^ 2) +
        Real.sqrt 2 / a0 * (20 * π / 3) * (3 * Real.sqrt (π / b) / (4 * b ^ 2)) +
        (32 * π ^ 2 / 9 + 8 * π / a0 ^ 2) * (2 / b ^ 3) +
        Real.sqrt 2 / a0 * (32 * π ^ 2 / 3) * (15 * Real.sqrt (π / b) / (8 * b ^ 3)) +
        16 * π ^ 2 / a0 ^ 2 * (6 / b ^ 4) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cS]
  norm_num
  rw [gaussMom_1 hb, gaussMom_2 hb, gaussMom_3 hb, gaussMom_4 hb, gaussMom_5 hb, gaussMom_6 hb,
    gaussMom_7 hb]
  ring



/-! ## 5. Numerics -/

theorem IS_mono {a0 β σ q r βU σU qU rU : ℝ} (ha0 : 0 < a0) (hβ0 : 0 ≤ β) (hσ0 : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hβ : β ≤ βU) (hσ : σ ≤ σU) (hq : q ≤ qU) (hr : r ≤ rU) :
    1 / 2 * β + r / a0 * (σ * β / 2) + (8 * q / 3 + 1 / a0 ^ 2) * β ^ 2 +
        r / a0 * (20 * q / 3) * (3 * σ * β ^ 2 / 4) + (32 * q ^ 2 / 9 + 8 * q / a0 ^ 2) * (2 * β ^ 3) +
        r / a0 * (32 * q ^ 2 / 3) * (15 * σ * β ^ 3 / 8) + 16 * q ^ 2 / a0 ^ 2 * (6 * β ^ 4) ≤
      1 / 2 * βU + rU / a0 * (σU * βU / 2) + (8 * qU / 3 + 1 / a0 ^ 2) * βU ^ 2 +
        rU / a0 * (20 * qU / 3) * (3 * σU * βU ^ 2 / 4) +
        (32 * qU ^ 2 / 9 + 8 * qU / a0 ^ 2) * (2 * βU ^ 3) +
        rU / a0 * (32 * qU ^ 2 / 3) * (15 * σU * βU ^ 3 / 8) + 16 * qU ^ 2 / a0 ^ 2 * (6 * βU ^ 4) := by
  have hβU : 0 ≤ βU := hβ0.trans hβ
  have hσU : 0 ≤ σU := hσ0.trans hσ
  have hqU : 0 ≤ qU := hq0.trans hq
  have hrU : 0 ≤ rU := hr0.trans hr
  gcongr

theorem IS_reshape (a0 b s r q : ℝ) :
    1 / 2 * (1 / b) + r / a0 * (s / (2 * b)) + (8 * q / 3 + 1 / a0 ^ 2) * (1 / b ^ 2) +
        r / a0 * (20 * q / 3) * (3 * s / (4 * b ^ 2)) + (32 * q ^ 2 / 9 + 8 * q / a0 ^ 2) * (2 / b ^ 3) +
        r / a0 * (32 * q ^ 2 / 3) * (15 * s / (8 * b ^ 3)) + 16 * q ^ 2 / a0 ^ 2 * (6 / b ^ 4) =
      1 / 2 * (1 / b) + r / a0 * (s * (1 / b) / 2) + (8 * q / 3 + 1 / a0 ^ 2) * (1 / b) ^ 2 +
        r / a0 * (20 * q / 3) * (3 * s * (1 / b) ^ 2 / 4) +
        (32 * q ^ 2 / 9 + 8 * q / a0 ^ 2) * (2 * (1 / b) ^ 3) +
        r / a0 * (32 * q ^ 2 / 3) * (15 * s * (1 / b) ^ 3 / 8) + 16 * q ^ 2 / a0 ^ 2 * (6 * (1 / b) ^ 4) := by
  ring

theorem sum_cS_gauss_le {a0 : ℝ} (ha0 : 0 < a0) :
    ∑ j ∈ Finset.range 8, cS a0 j * gaussMom (4 * π - 37 / 10) j ≤
      1 / 2 * (10000 / 88660) + 141422 / 100000 / a0 * (5953 / 10000 * (10000 / 88660) / 2) +
        (8 * (31416 / 10000) / 3 + 1 / a0 ^ 2) * (10000 / 88660) ^ 2 +
        141422 / 100000 / a0 * (20 * (31416 / 10000) / 3) *
          (3 * (5953 / 10000) * (10000 / 88660) ^ 2 / 4) +
        (32 * (31416 / 10000) ^ 2 / 9 + 8 * (31416 / 10000) / a0 ^ 2) * (2 * (10000 / 88660) ^ 3) +
        141422 / 100000 / a0 * (32 * (31416 / 10000) ^ 2 / 3) *
          (15 * (5953 / 10000) * (10000 / 88660) ^ 3 / 8) +
        16 * (31416 / 10000) ^ 2 / a0 ^ 2 * (6 * (10000 / 88660) ^ 4) := by
  have hb : (0 : ℝ) < 4 * π - 37 / 10 := by linarith [Real.pi_gt_d2]
  rw [sum_cS_gauss a0 hb]
  have hβ : 1 / (4 * π - 37 / 10) ≤ 10000 / 88660 := by
    rw [div_le_div_iff₀ hb (by norm_num)]
    have := Real.pi_gt_d4
    norm_num at this ⊢
    linarith
  have hs : Real.sqrt (π / (4 * π - 37 / 10)) ≤ 5953 / 10000 := by
    calc Real.sqrt (π / (4 * π - 37 / 10)) ≤ Real.sqrt ((5953 / 10000) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ hb]
          have := Real.pi_gt_d4
          norm_num at this ⊢
          linarith
      _ = 5953 / 10000 := Real.sqrt_sq (by norm_num)
  have hpi : π ≤ 31416 / 10000 := by
    have := Real.pi_lt_d4
    norm_num at this ⊢
    linarith
  rw [IS_reshape a0 (4 * π - 37 / 10) (Real.sqrt (π / (4 * π - 37 / 10))) (Real.sqrt 2) π]
  exact IS_mono ha0 (one_div_pos.mpr hb).le (Real.sqrt_nonneg _)
    Real.pi_pos.le (Real.sqrt_nonneg _) hβ hs hpi sqrt_two_le_141422



theorem IS_26_le : ∑ j ∈ Finset.range 8, cS 26 j * gaussMom (4 * π - 37 / 10) j ≤ 2816 / 10000 :=
  (sum_cS_gauss_le (by norm_num)).trans (by norm_num)



theorem far_main_le {a : ℝ} (ha : 26 ≤ a) :
    5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 100000 / a := by
  have ha0 : 0 < a := by linarith
  have hpi1 := Real.pi_gt_d2
  set x := π * a ^ 2 / 18 with hx
  have ha2 : 676 ≤ a ^ 2 := by nlinarith
  have hx117 : 117 ≤ x := by
    rw [hx, le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hpi1.le (sq_nonneg a)]
  have hax : a ≤ x := by
    have h81 : 81 ≤ π * a := by nlinarith
    rw [hx]
    nlinarith
  have hexp : Real.exp (-x) ≤ 120 / x ^ 5 := by
    rw [Real.exp_neg]
    have h5 := Real.pow_div_factorial_le_exp x (by linarith) 5
    have hpos : 0 < x ^ 5 / (Nat.factorial 5) := by positivity
    calc (Real.exp x)⁻¹ ≤ (x ^ 5 / (Nat.factorial 5))⁻¹ := inv_anti₀ hpos h5
      _ = 120 / x ^ 5 := by norm_num [Nat.factorial]
  have hs2 : Real.sqrt (π / (π / 2)) = Real.sqrt 2 := by
    congr 1; field_simp
  rw [hs2, le_div_iff₀ ha0]
  have hx0 : 0 < x := by linarith
  calc 5 * Real.exp (-x) * Real.sqrt 2 * a ≤ 5 * (120 / x ^ 5) * (3 / 2) * x := by
        gcongr
        exact sqrt_two_le_three_halves
    _ = 900 / x ^ 4 := by field_simp; ring
    _ ≤ 1 / 100000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (117 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx117 4
        nlinarith

theorem main_term_le {a : ℝ} (ha : 0 < a) : 1 / (2 * π * a) * (49 / 120) ≤ 65 / 1000 / a := by
  rw [show 1 / (2 * π * a) * (49 / 120) = 49 / (240 * π) / a by field_simp; ring]
  apply div_le_div_of_nonneg_right _ ha.le
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have := Real.pi_gt_d4
  norm_num at this ⊢
  linarith

theorem etwo_term_le {a A c : ℝ} (hA : 0 < A) (ha : A ≤ a)
    (hc : 141422 / 100000 / (4 * 9869 / 1000) * (1 / A) ≤ c) :
    Real.sqrt 2 / (2 * π * a ^ 2) * (1 / (2 * π)) ≤ c / a := by
  have ha0 : 0 < a := by linarith
  have e : Real.sqrt 2 / (2 * π * a ^ 2) * (1 / (2 * π)) =
      Real.sqrt 2 / (4 * π ^ 2) * (1 / a) / a := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ ha0.le
  have hpp : (9869 / 1000 : ℝ) ≤ π ^ 2 := by
    have := Real.pi_gt_d4
    norm_num at this
    nlinarith
  have h1a : 1 / a ≤ 1 / A := one_div_le_one_div_of_le hA ha
  have hr2 := sqrt_two_le_141422
  calc Real.sqrt 2 / (4 * π ^ 2) * (1 / a) ≤ 141422 / 100000 / (4 * (9869 / 1000)) * (1 / A) := by
        gcongr
    _ ≤ c := by linarith

theorem second_term_le {a A d D IS ISU c : ℝ} (hA : 0 < A) (ha : A ≤ a) (hd : Real.exp d ≤ D)
    (hIS : IS ≤ ISU) (hISU : 0 ≤ ISU)
    (hc : 141422 / 100000 * D * ISU / (2 * (31415 / 10000)) * (1 / A) ≤ c) :
    Real.sqrt 2 * Real.exp d / (2 * π * a ^ 2) * IS ≤ c / a := by
  have ha0 : 0 < a := by linarith
  have hK : 0 ≤ Real.sqrt 2 * Real.exp d / (2 * π * a ^ 2) := by positivity
  refine (mul_le_mul_of_nonneg_left hIS hK).trans ?_
  have e : Real.sqrt 2 * Real.exp d / (2 * π * a ^ 2) * ISU =
      Real.sqrt 2 * Real.exp d * ISU / (2 * π) * (1 / a) / a := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ ha0.le
  have h1a : 1 / a ≤ 1 / A := one_div_le_one_div_of_le hA ha
  have hr2 := sqrt_two_le_141422
  have hD0 : 0 ≤ D := (Real.exp_pos d).le.trans hd
  have hpi : (31415 / 10000 : ℝ) ≤ π := by
    have := Real.pi_gt_d4
    norm_num at this
    linarith
  calc Real.sqrt 2 * Real.exp d * ISU / (2 * π) * (1 / a) ≤
      141422 / 100000 * D * ISU / (2 * (31415 / 10000)) * (1 / A) := by
        gcongr
    _ ≤ c := hc









/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/





/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/







/-! ## 8. The old headlines re-derived from the sharpened ones -/





end RSInt

namespace RSSeam

open RSInt

/-! ## 9. The seam, sharpened: t >= 509 (a >= 9) -/









end RSSeam

end

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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Absolute Gaussian moments -/





































/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/





































/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/
























theorem solution {a : ℝ} (ha : 26 ≤ a) :
    1 / (2 * π * a) * (∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j) +
      Real.sqrt 2 / (2 * π * a ^ 2) * (∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j) +
      Real.sqrt 2 * Real.exp (1 / (2 * 26 ^ 2)) / (2 * π * a ^ 2) *
        (∑ j ∈ Finset.range 8, cS 26 j * gaussMom (4 * π - 37 / 10) j) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 7 / 100 / a := by
  have ha0 : 0 < a := by linarith
  rw [sum_cMain_gauss, sum_cEtwo_gauss]
  have he : Real.exp (1 / (2 * 26 ^ 2)) ≤ 1352 / 1351 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / (2 * 26 ^ 2)) (by norm_num)
      (by norm_num)
    have e : (1 : ℝ) / (1 - 1 / (2 * 26 ^ 2)) = 1352 / 1351 := by norm_num
    linarith
  have t1 := main_term_le ha0
  have t2 := etwo_term_le (c := 139 / 100000) (by norm_num : (0 : ℝ) < 26) ha (by norm_num)
  have t3 := second_term_le (c := 246 / 100000) (by norm_num : (0 : ℝ) < 26) ha he IS_26_le
    (by norm_num) (by norm_num)
  have t4 := far_main_le ha
  have hsum : 65 / 1000 / a + 139 / 100000 / a + 246 / 100000 / a + 1 / 100000 / a ≤ 7 / 100 / a := by
    rw [show 65 / 1000 / a + 139 / 100000 / a + 246 / 100000 / a + 1 / 100000 / a =
      (65 / 1000 + 139 / 100000 + 246 / 100000 + 1 / 100000) / a by ring]
    exact div_le_div_of_nonneg_right (by norm_num) ha0.le
  linarith
