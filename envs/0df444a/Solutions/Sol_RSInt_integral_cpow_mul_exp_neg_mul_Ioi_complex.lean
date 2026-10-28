-- Prove2me | solution 1 for RSInt.integral_cpow_mul_exp_neg_mul_Ioi_complex
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:53:42.35578+00:00
-- url     : https://prove2.me/submissions/ac911132-85be-479b-93ff-5523ee052bfc

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

theorem solution {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * cexp (-(z * ρ)) = (1 / z) ^ s * Gamma s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set f : ℂ → ℂ := fun z => ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * cexp (-(z * ρ)) with hf
  set g : ℂ → ℂ := fun z => (1 / z) ^ s * Gamma s with hg
  -- continuity of the integrand in rho on (0, oo)
  have hcpow : ContinuousOn (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1)) (Ioi 0) := by
    intro ρ hρ
    exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hf_diff : DifferentiableOn ℂ f U := by
    intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    set r := z₀.re / 2 with hr
    have hr0 : 0 < r := by positivity
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun z (ρ : ℝ) => (ρ : ℂ) ^ (s - 1) * cexp (-(z * ρ)))
      (F' := fun z (ρ : ℝ) => (ρ : ℂ) ^ (s - 1) * (cexp (-(z * ρ)) * (-(ρ : ℂ))))
      (x₀ := z₀) (bound := fun ρ : ℝ => ρ ^ s.re * Real.exp (-(r * ρ)))
      (Metric.ball_mem_nhds z₀ hr0)
      (Eventually.of_forall fun z =>
        (hcpow.mul (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable measurableSet_Ioi)
      ?_ ((hcpow.mul (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable
        measurableSet_Ioi) ?_ (integrableOn_rpow_exp (by linarith) hr0) ?_
    · exact key.2.differentiableAt.differentiableWithinAt
    · -- integrability at z₀
      refine (integrableOn_rpow_exp (a := s.re - 1) (b := z₀.re) (by linarith) hz₀').mono'
        ((hcpow.mul (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable measurableSet_Ioi) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
      rw [norm_mul, norm_ofReal_cpow hρ, Complex.norm_exp]
      simp
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ z hz => ?_)
      have hρ' : (0 : ℝ) < ρ := hρ
      have hzre : r < z.re := by
        have h1 := Metric.mem_ball.mp hz
        rw [Complex.dist_eq] at h1
        have h2 := Complex.abs_re_le_norm (z - z₀)
        rw [Complex.sub_re] at h2
        have h3 := neg_abs_le (z.re - z₀.re)
        linarith
      rw [norm_mul, norm_mul, norm_ofReal_cpow hρ', Complex.norm_exp, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ']
      have hre : (-(z * (ρ : ℂ))).re = -(z.re * ρ) := by simp
      rw [hre]
      have hexp : Real.exp (-(z.re * ρ)) ≤ Real.exp (-(r * ρ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hpow : ρ ^ (s - 1).re * ρ = ρ ^ s.re := by
        rw [Complex.sub_re, Complex.one_re, Real.rpow_sub hρ', Real.rpow_one]
        field_simp
      calc ρ ^ (s - 1).re * (Real.exp (-(z.re * ρ)) * ρ)
          = ρ ^ (s - 1).re * ρ * Real.exp (-(z.re * ρ)) := by ring
        _ ≤ ρ ^ s.re * Real.exp (-(r * ρ)) := by
            rw [hpow]
            exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hρ'.le _)
    · refine Eventually.of_forall fun ρ z _ => ?_
      have h0 : HasDerivAt (fun z : ℂ => z * (ρ : ℂ)) (ρ : ℂ) z := by
        simpa using (hasDerivAt_id z).mul_const (ρ : ℂ)
      have h1 : HasDerivAt (fun z : ℂ => -(z * (ρ : ℂ))) (-(ρ : ℂ)) z := h0.neg
      exact h1.cexp.const_mul _
  have hg_diff : DifferentiableOn ℂ g U := by
    intro z hz
    have hz' : 0 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'
    have hmem : 1 / z ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      rw [one_div, Complex.inv_re]
      exact div_pos hz' (Complex.normSq_pos.mpr hz0)
    exact (((differentiableAt_const 1).div differentiableAt_id hz0).cpow
      (differentiableAt_const s) hmem).mul_const _ |>.differentiableWithinAt
  have hagree : ∀ r : ℝ, 0 < r → f r = g r := by
    intro r hr
    simp only [hf, hg]
    exact integral_cpow_mul_exp_neg_mul_Ioi hs hr
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = g w := by
    have ht : Tendsto (fun k : ℕ => (((1 : ℝ) + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
        rw [add_zero] at h0
        have := (Complex.continuous_ofReal.tendsto 1).comp h0
        rw [Complex.ofReal_one] at this
        exact this
      · refine Eventually.of_forall fun k => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 : ((1 : ℝ) + 1 / ((k : ℝ) + 1)) = 1 := by exact_mod_cast h
        have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    exact ht.frequently (Frequently.of_forall fun k => hagree _ (by positivity))
  exact (hf_diff.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hg_diff.analyticOnNhd hUo) hpre h1U hfreq hz
