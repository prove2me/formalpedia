-- Prove2me | solution 1 for RSInt.continuousAt_rsH_cpow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:51:51.229525+00:00
-- url     : https://prove2.me/submissions/fbeafb38-dfc4-4860-a5cd-b1773e9921ce

import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_deriv_rsD_int_ne_zero
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

theorem rsD_int (n : ℤ) : rsD n = 0 := (rsD_eq_zero_iff _).mpr ⟨n, rfl⟩

theorem differentiable_rsD : Differentiable ℂ rsD := by
  unfold rsD; fun_prop













/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



end RSInt

end

/-  RS_Fold.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 4:
    the chi-side line.  Mathlib-only (imports `RS_Mellin`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `norm_cpow_le_exp` : ‖x^w‖ <= e^{pi |Im w|} e^{Re w ‖x‖} for Re w >= 0 (growth of x^w).
      * `continuousAt_rsH_cpow_zero` : for Re s > 2 the chi-side integrand rsH(x) x^(s-1) is
        continuous at the pole x = 0 of rsH (removable via dslope, value 0).
      * `lineDn_zero_fold` : FOLDING.  For Re s > 2 the chi-side integral along the line through 0
        is (1 + e^{i pi s}) times the half-line integral:
            lineDn 0 (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s
        (rsH is odd, and (-x)^(s-1) = x^(s-1) e^{i pi (s-1)} on that line).
      * `lineDn_zero_eq` : the line through 0 may be moved to any c in (0, 1) (strip Cauchy; the
        pole at 0 sits on the boundary and is harmless for Re s > 2).
      * `lineDn_eq_fold` : lineDn c (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s, 0 < c < 1, Re s > 2.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Growth of `x^w` -/



/-! ## 2. Continuity of the chi-side integrand at 0 -/



theorem solution {s : ℂ} (hs : 2 < s.re) :
    ContinuousAt (fun x => rsH x * x ^ (s - 1)) 0 := by
  set D₁ := dslope rsD 0 with hD₁
  have hD₁0 : D₁ 0 ≠ 0 := by
    rw [hD₁, dslope_same]
    have := deriv_rsD_int_ne_zero 0
    simpa using this
  have hD₁c : ContinuousAt D₁ 0 := continuousAt_dslope_same.mpr (differentiable_rsD 0)
  have hs2 : s - 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set G : ℂ → ℂ := fun x => cexp (-(↑π * I * x ^ 2)) * x ^ (s - 2) / D₁ x with hG
  have hGc : ContinuousAt G 0 := by
    have hc1 : ContinuousAt (fun x : ℂ => x ^ (s - 2)) 0 := by
      have h := continuousAt_cpow_zero_of_re_pos (z := s - 2) (by simp; linarith)
      exact h.comp (f := fun x : ℂ => (x, s - 2)) (by fun_prop)
    exact ((by fun_prop : ContinuousAt (fun x : ℂ => cexp (-(↑π * I * x ^ 2))) 0).mul hc1).div
      hD₁c hD₁0
  refine hGc.congr ?_
  have hball : ∀ᶠ x in 𝓝 (0 : ℂ), ‖x‖ < 1 / 2 := by
    have := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [this] with x hx
    simpa using hx
  filter_upwards [hball] with x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [hG, Complex.zero_cpow hs2, Complex.zero_cpow hs1, mul_zero, zero_div]
  · have hD : rsD x ≠ 0 := by
      intro h0
      obtain ⟨n, rfl⟩ := (rsD_eq_zero_iff x).mp h0
      have hn : |(n : ℝ)| < 1 / 2 := by simpa using hx
      have hn0 : n = 0 := by
        have h1 : (n : ℝ) < 1 / 2 := lt_of_le_of_lt (le_abs_self _) hn
        have h2 : -(1 / 2 : ℝ) < n := by linarith [neg_abs_le (n : ℝ)]
        have h3 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
        have h4 : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
        omega
      exact hx0 (by rw [hn0]; simp)
    have h00 : rsD 0 = 0 := by have := rsD_int 0; simpa using this
    have hdsl : D₁ x = rsD x / x := by
      rw [hD₁, dslope_of_ne _ hx0, slope_def_field, h00, sub_zero, sub_zero]
    simp only [hG]
    unfold rsH
    rw [hdsl, show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    field_simp
