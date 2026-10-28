-- Prove2me | solution 1 for RSInt.rsK_split
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:23:52.959378+00:00
-- url     : https://prove2.me/submissions/20b106bc-6b21-4e74-8be7-9092b1e01780

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_lineUp_mordell
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









/-! ## 2. Branch bookkeeping -/







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/













/-! ## 5. Splitting the Mordell kernel -/

theorem norm_exp_one_add_I_mul (ρ : ℝ) : ‖cexp ((1 + I) * ρ)‖ = Real.exp ρ := by
  rw [Complex.norm_exp]; simp

theorem exp_one_add_I_ne_one {ρ : ℝ} (hρ : 0 < ρ) : cexp ((1 + I) * ρ) ≠ 1 := by
  intro h
  have := norm_exp_one_add_I_mul ρ
  rw [h, norm_one] at this
  have h2 : (1 : ℝ) < Real.exp ρ := Real.one_lt_exp_iff.mpr hρ
  linarith



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







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/













/-! ## 5. Splitting the Mordell kernel -/






theorem solution {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    rsK c ((1 + I) * ρ) = -(1 / (cexp ((1 + I) * ρ) - 1)) +
      cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π)) /
        (cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))) := by
  set y : ℂ := (1 + I) * ρ with hy
  have hM := lineUp_mordell hc hc1 y
  set u := cexp (y / 2) with hu
  set G := cexp (I * y ^ 2 / (4 * ↑π)) with hG
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hneg : cexp (-y / 2) = u⁻¹ := by rw [neg_div, Complex.exp_neg]
  have hneg' : cexp (-(y / 2)) = u⁻¹ := Complex.exp_neg _
  have hyy : cexp y = u * u := by rw [hu, ← Complex.exp_add]; ring_nf
  have hne1 : u * u ≠ 1 := by rw [← hyy]; exact exp_one_add_I_ne_one hρ
  have hd1 : u⁻¹ - u ≠ 0 := by
    intro h
    apply hne1
    have : u⁻¹ = u := sub_eq_zero.mp h
    calc u * u = u * u⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel₀ hu0
  have hd2 : u - u⁻¹ ≠ 0 := by
    intro h; apply hd1; rw [← neg_sub, h, neg_zero]
  have hd3 : u * u - 1 ≠ 0 := sub_ne_zero.mpr hne1
  unfold rsK
  rw [hneg] at hM
  rw [hyy, hneg']
  have hK : lineUp c (fun x => rsG x * cexp (-(x * y))) = (u⁻¹ - G) / (u⁻¹ - u) := by
    rw [eq_div_iff hd1]; exact hM
  rw [hK, div_eq_iff hd1]
  have e0 : u⁻¹ - u = -u⁻¹ * (u * u - 1) := by field_simp; ring
  have e1 : 1 / (u * u - 1) * (u⁻¹ - u) = -u⁻¹ := by
    rw [e0, one_div, mul_comm, mul_assoc, mul_inv_cancel₀ hd3, mul_one]
  have e2 : G / (u - u⁻¹) * (u⁻¹ - u) = -G := by
    rw [show u⁻¹ - u = -(u - u⁻¹) by ring, mul_neg, div_mul_cancel₀ _ hd2]
  linear_combination e1 - e2
