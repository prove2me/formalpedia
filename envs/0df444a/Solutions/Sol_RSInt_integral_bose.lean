-- Prove2me | solution 1 for RSInt.integral_bose
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:05:24.971441+00:00
-- url     : https://prove2.me/submissions/4ae4041c-c615-45ce-9948-c52f37ad911c

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integral_cpow_mul_exp_neg_mul_Ioi_complex
import Theorems.Thm_RSInt_one_div_mul_cpow
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

theorem integrableOn_rpow_exp {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntegrableOn (fun ρ : ℝ => ρ ^ a * Real.exp (-(b * ρ))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) ha (by norm_num) hb
  refine this.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem norm_ofReal_cpow {ρ : ℝ} (hρ : 0 < ρ) (s : ℂ) : ‖(ρ : ℂ) ^ s‖ = ρ ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hρ s





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

theorem cpow_nat_succ_mul {k : ℕ} (s : ℂ) :
    (1 / (((k : ℂ) + 1) * (1 + I))) ^ s = 1 / ((k : ℂ) + 1) ^ s * (1 + I) ^ (-s) := by
  have hre : 0 < (((k : ℂ) + 1) * (1 + I)).re := by simp; positivity
  rw [one_div_mul_cpow hre, Complex.cpow_neg, one_div]



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







/-! ## 6. The Bose integral -/



theorem solution {s : ℂ} (hs : 1 < s.re) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) =
      (1 + I) ^ (-s) * Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  set f : ℕ → ℝ → ℂ := fun k ρ => (ρ : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * (1 + I) * ρ)) with hf
  have hser : ∀ ρ : ℝ, 0 < ρ →
      HasSum (fun k => f k ρ) ((ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1))) := by
    intro ρ hρ
    set q := cexp (-((1 + I) * ρ)) with hq
    have hqn : ‖q‖ < 1 := by
      rw [hq, Complex.norm_exp]
      simp only [neg_re, mul_re, add_re, one_re, I_re, ofReal_re, add_im, one_im, I_im, ofReal_im]
      simp only [add_zero, one_mul, mul_zero, sub_zero, zero_add]
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    have h1 := (hasSum_geometric_of_norm_lt_one hqn).mul_left ((ρ : ℂ) ^ (s - 1) * q)
    have hE0 : cexp ((1 + I) * ρ) ≠ 0 := Complex.exp_ne_zero _
    have hE1 : cexp ((1 + I) * ρ) - 1 ≠ 0 := sub_ne_zero.mpr (exp_one_add_I_ne_one hρ)
    have hqinv : q = (cexp ((1 + I) * ρ))⁻¹ := by rw [hq, Complex.exp_neg]
    have h1q : 1 - q ≠ 0 := by
      rw [hqinv]; intro h
      apply exp_one_add_I_ne_one hρ
      have := sub_eq_zero.mp h
      field_simp at this
      exact this
    have hfun : (fun k => f k ρ) = fun i => (ρ : ℂ) ^ (s - 1) * q * q ^ i := by
      ext k
      simp only [hf]
      rw [show (ρ : ℂ) ^ (s - 1) * q * q ^ k = (ρ : ℂ) ^ (s - 1) * q ^ (k + 1) by ring, hq,
        ← Complex.exp_nat_mul]
      congr 2; push_cast; ring
    have hval : (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) =
        (ρ : ℂ) ^ (s - 1) * q * (1 - q)⁻¹ := by
      rw [hqinv]; field_simp
    rw [hfun, hval]; exact h1
  have hint : ∀ k : ℕ, Integrable (f k) (volume.restrict (Ioi (0 : ℝ))) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    refine (integrableOn_rpow_exp (a := s.re - 1) (b := (k : ℝ) + 1) (by linarith) hk).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro ρ hρ
      exact (((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
        Complex.continuous_ofReal.continuousAt).mul (by fun_prop)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
      simp only [hf]
      rw [norm_mul, norm_ofReal_cpow hρ, Complex.norm_exp]
      apply le_of_eq
      congr 2
      simp
  have hnorm : ∀ k : ℕ, ∫ ρ in Ioi (0 : ℝ), ‖f k ρ‖ =
      (1 / ((k : ℝ) + 1)) ^ s.re * Real.Gamma s.re := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 hk]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    simp only [hf]
    rw [norm_mul, norm_ofReal_cpow hρ, Complex.norm_exp]
    congr 2
    simp
  have hsum : Summable (fun k : ℕ => ∫ ρ in Ioi (0 : ℝ), ‖f k ρ‖) := by
    simp_rw [hnorm]
    refine Summable.mul_right _ ?_
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) :=
      Real.summable_one_div_nat_rpow.mpr hs
    have h2 := (summable_nat_add_iff 1).mpr h1
    refine h2.congr (fun k => ?_)
    push_cast
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
  have hval : ∀ k : ℕ, ∫ ρ in Ioi (0 : ℝ), f k ρ =
      1 / ((k : ℂ) + 1) ^ s * (1 + I) ^ (-s) * Gamma s := by
    intro k
    have hre : 0 < (((k : ℂ) + 1) * (1 + I)).re := by simp; positivity
    simp only [hf]
    rw [integral_cpow_mul_exp_neg_mul_Ioi_complex hs0 hre, cpow_nat_succ_mul]
  calc ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1))
      = ∫ ρ in Ioi (0 : ℝ), ∑' k, f k ρ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
        exact (hser ρ hρ).tsum_eq.symm
    _ = ∑' k, ∫ ρ in Ioi (0 : ℝ), f k ρ := (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ s * ((1 + I) ^ (-s) * Gamma s) := by
        congr 1; ext k; rw [hval]; ring
    _ = (1 + I) ^ (-s) * Gamma s * riemannZeta s := by
        rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hs]; ring
