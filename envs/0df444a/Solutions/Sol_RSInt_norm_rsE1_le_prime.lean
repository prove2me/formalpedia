-- Prove2me | solution 1 for RSInt.norm_rsE1_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:22:09.63669+00:00
-- url     : https://prove2.me/submissions/10829215-d63f-4ae6-9417-7718546fe5ac

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
import Theorems.Thm_RSInt_norm_E1_integrand_near_prime
import Theorems.Thm_RSSeam_norm_E1_integrand_far
namespace RSInt
end RSInt
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



theorem integrable_abs_pow_mul_exp {b : ℝ} (hb : 0 < b) (j : ℕ) :
    Integrable (fun v : ℝ => |v| ^ j * Real.exp (-b * v ^ 2)) := by
  have hj : (-1 : ℝ) < j := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hj
  simp only [Real.rpow_natCast] at h
  refine h.abs.congr (Eventually.of_forall fun v => ?_)
  simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]





























/-- Integrals of polynomials in `|v|` against a Gaussian, term by term. -/
theorem integrable_poly_gauss {b : ℝ} (hb : 0 < b) (n : ℕ) (c : ℕ → ℝ) :
    Integrable (fun v : ℝ => (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2)) := by
  have e : (fun v : ℝ => (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2)) =
      fun v => ∑ j ∈ Finset.range n, c j * (|v| ^ j * Real.exp (-b * v ^ 2)) := by
    ext v; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e]
  exact integrable_finsetSum _ fun j _ => (integrable_abs_pow_mul_exp hb j).const_mul _

theorem integral_poly_gauss {b : ℝ} (hb : 0 < b) (n : ℕ) (c : ℕ → ℝ) :
    ∫ v : ℝ, (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2) =
      ∑ j ∈ Finset.range n, c j * gaussMom b j := by
  have e : (fun v : ℝ => (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2)) =
      fun v => ∑ j ∈ Finset.range n, c j * (|v| ^ j * Real.exp (-b * v ^ 2)) := by
    ext v; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e, integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]; rfl
  · intro j _; exact (integrable_abs_pow_mul_exp hb j).const_mul _

/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/











theorem sum_cMain (r : ℝ) :
    ∑ j ∈ Finset.range 5, cMain j * r ^ j = 41 / 40 - 10 * π / 3 * r ^ 2 + 40 * π ^ 2 / 9 * r ^ 4 := by
  simp [Finset.sum_range_succ, cMain]
  ring

theorem sum_cEtwo (r : ℝ) : ∑ j ∈ Finset.range 4, cEtwo j * r ^ j = r + 4 * π * r ^ 3 := by
  simp [Finset.sum_range_succ, cEtwo]

theorem sum_cS (a0 r : ℝ) :
    ∑ j ∈ Finset.range 8, cS a0 j * r ^ j =
      r * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * r ^ 2) + (r + 4 * π * r ^ 3) / a0) ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [Finset.sum_range_succ, cS]
  linear_combination (-(r * (1 + 8 * π / 3 * r ^ 2) ^ 2 / 4)) * hs

theorem qMain_nonneg (r : ℝ) : 0 ≤ 41 / 40 - 10 * π / 3 * r ^ 2 + 40 * π ^ 2 / 9 * r ^ 4 := by
  nlinarith [sq_nonneg (π * r ^ 2 - 3 / 8), Real.pi_pos]



















/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/





























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










theorem solution {a0 a p : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) :
    ‖rsE1 a p‖ ≤ 1 / (2 * π * a) * (∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j) +
      Real.sqrt 2 / (2 * π * a ^ 2) * (∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        (∑ j ∈ Finset.range 8, cS a0 j * gaussMom (4 * π - 37 / 10) j) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) := by
  have ha9 : 9 ≤ a := le_trans h9 ha
  have ha0 : 0 < a := by linarith
  have hb1 : (0 : ℝ) < 4 * π := by positivity
  have hb2 : (0 : ℝ) < 4 * π - 37 / 10 := by linarith [Real.pi_gt_d2]
  have hA : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2))) :=
    (integrable_poly_gauss hb1 5 cMain).const_mul _
  have hB : Integrable (fun v : ℝ => Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2))) :=
    (integrable_poly_gauss hb1 4 cEtwo).const_mul _
  have hC : Integrable (fun v : ℝ => Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2))) :=
    (integrable_poly_gauss hb2 8 (cS a0)).const_mul _
  have hD : Integrable (fun v : ℝ => 5 * Real.exp (-(π * a ^ 2 / 18)) *
      Real.exp (-(π / 2) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have hAB : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2))) := hA.add hB
  have hABC : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2))) :=
    hAB.add hC
  have hint : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2)) := hABC.add hD
  have hpt : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) /
      rsD (p + (v : ℂ) * (1 + I)) * (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      1 / (2 * π * a) *
        ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by
    intro v
    have n1 : 0 ≤ 1 / (2 * π * a) *
        ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) := by
      rw [sum_cMain]
      exact mul_nonneg (by positivity) (mul_nonneg (qMain_nonneg _) (Real.exp_pos _).le)
    have n2 : 0 ≤ Real.sqrt 2 / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) := by
      rw [sum_cEtwo]; positivity
    have n3 : 0 ≤ Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by
      rw [sum_cS]; positivity
    have n4 : 0 ≤ 5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by positivity
    rcases le_total |v| (a / 3) with hv | hv
    · have := _root_.RSInt.norm_E1_integrand_near_prime (p := p) h9 ha hv
      linarith
    · have := RSSeam.norm_E1_integrand_far (p := p) ha9 hv
      linarith
  unfold rsE1 lineUp
  simp only [ofReal_zero, zero_add]
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)) (le_of_eq ?_)
  rw [integral_add hABC hD, integral_add hAB hC, integral_add hA hB, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_poly_gauss hb1,
    integral_poly_gauss hb1, integral_poly_gauss hb2, integral_gaussian]
