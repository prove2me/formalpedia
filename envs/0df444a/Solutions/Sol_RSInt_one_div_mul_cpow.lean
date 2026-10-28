-- Prove2me | solution 1 for RSInt.one_div_mul_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:03:33.471415+00:00
-- url     : https://prove2.me/submissions/0bbaddd2-ecc1-47f8-a9a7-2589e6277ef0

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
/-  RS_Mellin.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 3:
    the Mellin step.  Mathlib-only (imports `RS_Kernel`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integral_cpow_mul_exp_neg_mul_Ioi_complex` : the complex-scaled Gamma integral
            int_0^oo rho^(s-1) e^(-z rho) d rho = (1/z)^s Gamma(s),     Re s > 0, Re z > 0,
        extending Mathlib's real-`z` lemma by the identity theorem.
      * `one_div_mul_cpow` : the branch bookkeeping (1/(x(1+i)))^s = x^(-s) (1+i)^(-s) whenever
        Re(x(1+i)) > 0.
      * `mellin_step` : Fubini on (line) x (0, oo):
            Gamma(s) lineUp c (rsG x^(-s)) = (1+i)^s int_0^oo rho^(s-1) rsK c ((1+i) rho) d rho,
        with rsK c y = lineUp c (rsG e^(-x y)) the Mordell integral.
      * `rsK_split` : the Mordell closed form at y = (1+i) rho, split into the Bose kernel and the
        Gaussian (chi-side) kernel.
      * `integral_bose` : int_0^oo rho^(s-1) / (e^((1+i) rho) - 1) = (1+i)^(-s) Gamma(s) zeta(s),
        Re s > 1 (geometric series, termwise integration, Mathlib's Dirichlet series for zeta).
      * `integral_Epart` : the chi-side kernel integral equals (2 pi)^s (1-i)^(-s) rsHR s, where
        rsHR s = int_0^oo rsH(r(1-i)) (r(1-i))^(s-1) (1-i) dr is half of the chi-side line.
      * `mellin_identity` : for Re s > 1 and 0 < c < 1,
            Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s.

    conjecture1_proved = False.  Classical integral identities for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. Integrability of `rho^a e^(-b rho)` and norms -/





theorem one_add_I_ne_zero : (1 + I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this



/-! ## 2. Branch bookkeeping -/

theorem arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ π := by
  have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  intro h; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]

theorem one_div_cpow_eq {z : ℂ} (hz : 0 < z.re) (s : ℂ) : (1 / z) ^ s = z ^ (-s) := by
  rw [one_div, Complex.inv_cpow _ _ (arg_ne_pi_of_re_pos hz), Complex.cpow_neg]



/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/













/-! ## 5. Splitting the Mordell kernel -/







/-! ## 6. The Bose integral -/





/-! ## 7. The chi-side kernel -/













/-! ## 8. Integrability of the two pieces on (0, oo) -/











/-! ## 9. The Mellin identity -/



end RSInt

end

/-  RS_Mellin.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 3:
    the Mellin step.  Mathlib-only (imports `RS_Kernel`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integral_cpow_mul_exp_neg_mul_Ioi_complex` : the complex-scaled Gamma integral
            int_0^oo rho^(s-1) e^(-z rho) d rho = (1/z)^s Gamma(s),     Re s > 0, Re z > 0,
        extending Mathlib's real-`z` lemma by the identity theorem.
      * `one_div_mul_cpow` : the branch bookkeeping (1/(x(1+i)))^s = x^(-s) (1+i)^(-s) whenever
        Re(x(1+i)) > 0.
      * `mellin_step` : Fubini on (line) x (0, oo):
            Gamma(s) lineUp c (rsG x^(-s)) = (1+i)^s int_0^oo rho^(s-1) rsK c ((1+i) rho) d rho,
        with rsK c y = lineUp c (rsG e^(-x y)) the Mordell integral.
      * `rsK_split` : the Mordell closed form at y = (1+i) rho, split into the Bose kernel and the
        Gaussian (chi-side) kernel.
      * `integral_bose` : int_0^oo rho^(s-1) / (e^((1+i) rho) - 1) = (1+i)^(-s) Gamma(s) zeta(s),
        Re s > 1 (geometric series, termwise integration, Mathlib's Dirichlet series for zeta).
      * `integral_Epart` : the chi-side kernel integral equals (2 pi)^s (1-i)^(-s) rsHR s, where
        rsHR s = int_0^oo rsH(r(1-i)) (r(1-i))^(s-1) (1-i) dr is half of the chi-side line.
      * `mellin_identity` : for Re s > 1 and 0 < c < 1,
            Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s.

    conjecture1_proved = False.  Classical integral identities for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Integrability of `rho^a e^(-b rho)` and norms -/









/-! ## 2. Branch bookkeeping -/






theorem solution {x : ℂ} (hx : 0 < (x * (1 + I)).re) (s : ℂ) :
    (1 / (x * (1 + I))) ^ s = x ^ (-s) * (1 + I) ^ (-s) := by
  set z := x * (1 + I) with hz
  have hz0 : z ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hx0 : x ≠ 0 := by intro h; rw [h, zero_mul] at hz; exact hz0 hz
  set w : ℂ := (1 + I)⁻¹ with hw
  have hw0 : w ≠ 0 := inv_ne_zero one_add_I_ne_zero
  have hwre : 0 < w.re := by rw [hw, Complex.inv_re]; simp [Complex.normSq_apply]
  have hxzw : x = z * w := by rw [hz, hw, mul_assoc, mul_inv_cancel₀ one_add_I_ne_zero, mul_one]
  have hargz := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hargw := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hlog : Complex.log x = Complex.log z + Complex.log w := by
    rw [hxzw]
    refine (Complex.log_mul_eq_add_log_iff hz0 hw0).mpr ⟨?_, ?_⟩
    · linarith [(abs_lt.mp hargz).1, (abs_lt.mp hargw).1, Real.pi_pos]
    · linarith [(abs_lt.mp hargz).2, (abs_lt.mp hargw).2, Real.pi_pos]
  have hlogw : Complex.log w = -Complex.log (1 + I) := by
    rw [hw, Complex.log_inv _ (arg_ne_pi_of_re_pos (by simp))]
  rw [one_div_cpow_eq hx, Complex.cpow_def_of_ne_zero hz0, Complex.cpow_def_of_ne_zero hx0,
    Complex.cpow_def_of_ne_zero one_add_I_ne_zero, hlog, hlogw, ← Complex.exp_add]
  congr 1; ring
