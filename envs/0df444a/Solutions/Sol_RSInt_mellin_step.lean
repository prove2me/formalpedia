-- Prove2me | solution 1 for RSInt.mellin_step
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:05:30.839214+00:00
-- url     : https://prove2.me/submissions/245684e6-794c-4c9c-92cb-062aeabe22da

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
import Theorems.Thm_RSInt_integral_cpow_mul_exp_neg_mul_Ioi_complex
import Theorems.Thm_RSInt_one_div_mul_cpow
/-  RS_Kernel.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 2:
    Riemann's kernels, their difference equations, Gaussian bounds, the Fresnel line integral,
    the pole-crossing lemmas and the Mordell closed form.

    Mathlib-only (imports `RS_Strip` only).

    ## The kernels

        rsD x = e^{i pi x} - e^{-i pi x}          (= 2 i sin(pi x); zeros exactly at the integers)
        rsG x = e^{ i pi x^2} / rsD x              (Riemann's kernel of the zeta integral)
        rsH x = e^{-i pi x^2} / rsD x              (the kernel of the chi-side integral)

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `rsD_eq_zero_iff`, `rsD_add_one`, `rsG_add_one`, `rsH_add_one` : zeros and the difference
        equations  rsG(x+1) = rsG x + e^{i pi (x^2+x)},  rsH(x+1) = rsH x - e^{-i pi (x^2+x)}.
      * `norm_rsG_le`, `norm_rsH_le` : on a slanted strip, away from the real axis (|Im x| >= 1), the
        kernels are bounded by exp(-2 pi (Im x)^2 + 2 pi D |Im x|)  (Gaussian decay).
      * `lineUp_fresnel`, `lineUp_gauss` : the Gaussian line integrals, e.g.
            lineUp c (x |-> e^{i pi (x^2+x) - x y}) = e^{y/2 + i y^2/(4 pi)}     (every c, every y).
      * `lineUp_same_gap`, `lineUp_cross` : moving the slope-(+1) line inside a gap (n, n+1) changes
        nothing; moving it across the pole at the integer n adds phi(n):
            lineUp c2 (rsG * phi) = lineUp c1 (rsG * phi) + phi n,   n-1 < c1 < n < c2 < n+1,
        for every phi holomorphic on the strip with at most exponential growth.  No residue theorem
        is used: the pole is removed by `dslope`, and the jump of the bare kernel is computed from
        the difference equation and the Fresnel integral.
      * `lineDn_same_gap`, `lineDn_cross` : the slope-(-1) analogues for rsH (by conjugation).
      * `lineUp_mordell` : the Mordell closed form, for 0 < c < 1 and every y:
            lineUp c (x |-> rsG x e^{-x y}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.

    conjecture1_proved = False.  Contour identities for one explicit kernel; nothing here bears
    on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. The kernels and their algebra -/









theorem rsD_eq_zero_iff (x : ℂ) : rsD x = 0 ↔ ∃ n : ℤ, x = n := by
  unfold rsD
  rw [sub_eq_zero, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * ↑π * I : ℂ) * x = (2 * ↑π * I) * n := by linear_combination hn
    exact mul_left_cancel₀ (by simp [I_ne_zero]) h2
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩



theorem differentiable_rsD : Differentiable ℂ rsD := by
  unfold rsD; fun_prop













/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn

theorem differentiableAt_rsG {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsG x := by
  unfold rsG
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (↑π * I * x ^ 2))) x).div
    (differentiable_rsD x) h



/-- A point of the slope-(+1) line through a non-integer `c` is never an integer. -/
theorem lineUp_pt_ne_int {c : ℝ} (hc : ∀ m : ℤ, (m : ℝ) ≠ c) (v : ℝ) (n : ℤ) :
    (c : ℂ) + v * (1 + I) ≠ n := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre
  exact hc n (by linarith)



theorem notInt_of_Ioo {c : ℝ} {n : ℤ} (h₁ : (n : ℝ) < c) (h₂ : c < n + 1) :
    ∀ m : ℤ, (m : ℝ) ≠ c := by
  intro m hm
  rw [← hm] at h₁ h₂
  have a : n < m := by exact_mod_cast h₁
  have b : m < n + 1 := by exact_mod_cast h₂
  omega

/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/





theorem integrable_lineUp_rsG {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Integrable (fun v : ℝ => rsG (c + v * (1 + I))) := by
  have := integrable_lineUp_rsG_mul (φ := fun _ => (1 : ℂ)) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩
    hcl (fun x _ => continuousAt_const) (A := 1) (B := 0) (fun x _ => by simp)
  simpa using this





/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



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

namespace RSInt

/-! ## 1. Integrability of `rho^a e^(-b rho)` and norms -/

theorem integrableOn_rpow_exp {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntegrableOn (fun ρ : ℝ => ρ ^ a * Real.exp (-(b * ρ))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) ha (by norm_num) hb
  refine this.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem norm_ofReal_cpow {ρ : ℝ} (hρ : 0 < ρ) (s : ℂ) : ‖(ρ : ℂ) ^ s‖ = ρ ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hρ s

theorem one_add_I_ne_zero : (1 + I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this



/-! ## 2. Branch bookkeeping -/







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/



theorem re_lineUp_mul (c v : ℝ) : (((c : ℂ) + v * (1 + I)) * (1 + I)).re = c := by
  simp

theorem cpow_mul_cpow_neg_one_add_I (s : ℂ) : (1 + I) ^ s * (1 + I) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => one_add_I_ne_zero h.1

theorem gamma_cpow_line {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    Gamma s * ((c : ℂ) + v * (1 + I)) ^ (-s) =
      (1 + I) ^ s * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) *
        cexp (-(((c : ℂ) + v * (1 + I)) * (1 + I) * ρ)) := by
  have hre : 0 < (((c : ℂ) + v * (1 + I)) * (1 + I)).re := by rw [re_lineUp_mul]; exact hc
  rw [integral_cpow_mul_exp_neg_mul_Ioi_complex hs hre, one_div_mul_cpow hre]
  have h1 := cpow_mul_cpow_neg_one_add_I s
  linear_combination (-(((c : ℂ) + v * (1 + I)) ^ (-s) * Gamma s)) * h1

theorem continuous_rsG_line {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Continuous (fun v : ℝ => rsG ((c : ℂ) + v * (1 + I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have h1 : ContinuousAt rsG ((c : ℂ) + v * (1 + I)) :=
    (differentiableAt_rsG (rsD_ne_zero_of_ne (lineUp_pt_ne_int hcl v))).continuousAt
  have h2 : ContinuousAt (fun v : ℝ => (c : ℂ) + v * (1 + I)) v := by fun_prop
  exact ContinuousAt.comp (g := rsG) (f := fun v : ℝ => (c : ℂ) + v * (1 + I)) h1 h2



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



/-! ## 4. The Mellin step (Fubini) -/












theorem solution {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s : ℂ} (hs : 0 < s.re) :
    Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      (1 + I) ^ s * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsK c ((1 + I) * ρ) := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ c :=
    notInt_of_Ioo (n := 0) (by simpa using hc) (by simpa using hc1)
  set F : ℝ → ℝ → ℂ := fun v ρ => rsG ((c : ℂ) + v * (1 + I)) * (1 + I) *
    ((ρ : ℂ) ^ (s - 1) * cexp (-(((c : ℂ) + v * (1 + I)) * (1 + I) * ρ))) with hF
  have hL : Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      (1 + I) ^ s * ∫ v : ℝ, ∫ ρ in Ioi (0 : ℝ), F v ρ := by
    unfold lineUp
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; ext v
    simp only [hF]
    rw [integral_const_mul]
    have := gamma_cpow_line hc hs v
    calc Gamma s * (rsG ((c : ℂ) + v * (1 + I)) * ((c : ℂ) + v * (1 + I)) ^ (-s) * (1 + I))
        = rsG ((c : ℂ) + v * (1 + I)) * (1 + I) * (Gamma s * ((c : ℂ) + v * (1 + I)) ^ (-s)) := by
          ring
      _ = _ := by rw [this]; ring
  -- integrability on the product
  have hf₁ : Integrable (fun v : ℝ => ‖rsG ((c : ℂ) + v * (1 + I)) * (1 + I)‖) :=
    ((integrable_lineUp_rsG hcl).mul_const (1 + I)).norm
  have hf₂ : Integrable (fun ρ : ℝ => ‖(ρ : ℂ) ^ (s - 1)‖ * Real.exp (-(c * ρ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine (integrableOn_rpow_exp (a := s.re - 1) (b := c) (by linarith) hc).congr_fun
      (fun ρ hρ => ?_) measurableSet_Ioi
    simp only
    rw [norm_ofReal_cpow hρ, Complex.sub_re, Complex.one_re]
  have hprod := hf₁.mul_prod hf₂
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : Measurable (fun p : ℝ × ℝ => rsG ((c : ℂ) + p.1 * (1 + I)) * (1 + I)) :=
      ((continuous_rsG_line hcl).measurable.comp measurable_fst).mul_const _
    have h2 : Measurable (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ (s - 1)) :=
      (Complex.measurable_ofReal.comp measurable_snd).pow_const _
    have h3 : Measurable (fun p : ℝ × ℝ =>
        cexp (-(((c : ℂ) + p.1 * (1 + I)) * (1 + I) * p.2))) :=
      (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        cexp (-(((c : ℂ) + p.1 * (1 + I)) * (1 + I) * p.2)))).measurable
    exact (h1.mul (h2.mul h3)).aestronglyMeasurable
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hre : ∀ v ρ : ℝ, (-(((c : ℂ) + v * (1 + I)) * (1 + I) * (ρ : ℂ))).re = -(c * ρ) := by
      intro v ρ; simp
    refine hprod.mono' hmeas (Eventually.of_forall fun p => le_of_eq ?_)
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, hre]
  rw [hL, integral_integral_swap hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => ?_)
  simp only [hF, rsK, lineUp]
  rw [← integral_const_mul]
  congr 1; ext v
  rw [show ((c : ℂ) + v * (1 + I)) * (1 + I) * (ρ : ℂ) = ((c : ℂ) + v * (1 + I)) * ((1 + I) * ρ) by
    ring]
  ring
