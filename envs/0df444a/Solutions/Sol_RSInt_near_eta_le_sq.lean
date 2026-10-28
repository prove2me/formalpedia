-- Prove2me | solution 1 for RSInt.near_eta_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:57:16.502981+00:00
-- url     : https://prove2.me/submissions/f6d58a02-0130-4b0c-84d8-415c0d716931

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

theorem sqrt_two_le_1415 : Real.sqrt 2 ≤ 1415 / 1000 := by
  calc Real.sqrt 2 ≤ Real.sqrt ((1415 / 1000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 1415 / 1000 := Real.sqrt_sq (by norm_num)



















theorem amgm_sqrt_two (r q : ℝ) : Real.sqrt 2 / 2 * r * q ≤ r ^ 2 / 4 + q ^ 2 / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := sq_nonneg (r - Real.sqrt 2 * q)
  have e : (r - Real.sqrt 2 * q) ^ 2 = r ^ 2 - 2 * Real.sqrt 2 * r * q + Real.sqrt 2 ^ 2 * q ^ 2 := by
    ring
  rw [e, hs] at h
  linarith

theorem coef_le_37_10 : 1 / 4 + 4 * Real.sqrt 2 * π / 9 + (4 * π / 9 + 1 / 81) ≤ 37 / 10 := by
  have h1 := sqrt_two_le_1415
  have h2 := Real.pi_lt_d4
  have h4 : Real.sqrt 2 * π ≤ 1415 / 1000 * 3.1416 :=
    mul_le_mul h1 h2.le Real.pi_pos.le (by norm_num)
  norm_num at h2 h4 ⊢
  linarith













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




























theorem solution {a0 a v : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) (hv : |v| ≤ a / 3) :
    Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
        (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) ≤
      37 / 10 * v ^ 2 + 1 / (2 * a0 ^ 2) := by
  have ha00 : 0 < a0 := by linarith
  have ha0 : 0 < a := by linarith
  have ha9 : 9 ≤ a := by linarith
  have hX0 : 0 ≤ 8 * π * v ^ 2 / 3 := by positivity
  have h1X : |1 - 8 * π * v ^ 2 / 3| ≤ 1 + 8 * π * v ^ 2 / 3 := by
    rw [abs_le]; constructor <;> linarith
  have he1u : Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a ≤
      Real.sqrt 2 / 2 * |v| * (1 + 8 * π * v ^ 2 / 3) / a := by gcongr
  have hra : |v| / a ≤ 1 / 3 := by rw [div_le_iff₀ ha0]; linarith
  have h1 : Real.sqrt 2 / 2 * |v| * (1 + 8 * π * v ^ 2 / 3) / a =
      Real.sqrt 2 / 2 * |v| / a + 4 * Real.sqrt 2 * π / 3 * v ^ 2 * (|v| / a) := by ring
  have h21 : Real.sqrt 2 / 2 * |v| / a ≤ Real.sqrt 2 / 2 * |v| / a0 :=
    div_le_div_of_nonneg_left (by positivity) ha00 ha
  have h22 := amgm_sqrt_two |v| (1 / a0)
  have e : Real.sqrt 2 / 2 * |v| * (1 / a0) = Real.sqrt 2 / 2 * |v| / a0 := by ring
  have e' : |v| ^ 2 / 4 + (1 / a0) ^ 2 / 2 = v ^ 2 / 4 + 1 / (2 * a0 ^ 2) := by
    rw [sq_abs]; field_simp
  rw [e, e'] at h22
  have h3 : 4 * Real.sqrt 2 * π / 3 * v ^ 2 * (|v| / a) ≤ 4 * Real.sqrt 2 * π / 3 * v ^ 2 * (1 / 3) :=
    mul_le_mul_of_nonneg_left hra (by positivity)
  have hva : v ^ 2 / a ^ 2 ≤ 1 / 9 := by
    have : (|v| / a) ^ 2 ≤ (1 / 3) ^ 2 := pow_le_pow_left₀ (by positivity) hra 2
    rw [div_pow, sq_abs] at this; linarith
  have ha81 : (81 : ℝ) ≤ a ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) ha9 2
    norm_num at this; linarith
  have hia : 1 / a ^ 2 ≤ 1 / 81 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have eB : π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2) =
      v ^ 2 * (1 / a ^ 2) + 4 * π * v ^ 2 * (v ^ 2 / a ^ 2) := by
    field_simp; ring
  have k1 := mul_le_mul_of_nonneg_left hia (sq_nonneg v)
  have k2 := mul_le_mul_of_nonneg_left hva (by positivity : (0 : ℝ) ≤ 4 * π * v ^ 2)
  have k := mul_le_mul_of_nonneg_right coef_le_37_10 (sq_nonneg v)
  rw [eB]
  linarith
