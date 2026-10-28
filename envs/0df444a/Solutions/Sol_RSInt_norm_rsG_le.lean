-- Prove2me | solution 1 for RSInt.norm_rsG_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:59:06.408983+00:00
-- url     : https://prove2.me/submissions/4eb0f5c4-d4c6-4061-93d0-84afda2b85fc

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
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



























/-! ## 2. Norm bounds -/

theorem norm_exp_piI_sq (x : ℂ) :
    ‖cexp (↑π * I * x ^ 2)‖ = Real.exp (-(2 * π * x.re * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [pow_two, mul_re, mul_im]; ring



theorem norm_exp_piI (x : ℂ) : ‖cexp (↑π * I * x)‖ = Real.exp (-(π * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]

theorem norm_exp_neg_piI (x : ℂ) : ‖cexp (-(↑π * I * x))‖ = Real.exp (π * x.im) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]

theorem norm_rsD_ge (x : ℂ) :
    Real.exp (π * |x.im|) - Real.exp (-(π * |x.im|)) ≤ ‖rsD x‖ := by
  unfold rsD
  rcases le_total 0 x.im with h | h
  · rw [abs_of_nonneg h]
    have := norm_sub_norm_le (cexp (-(↑π * I * x))) (cexp (↑π * I * x))
    rw [norm_exp_piI, norm_exp_neg_piI, norm_sub_rev] at this
    linarith
  · rw [abs_of_nonpos h, mul_neg, neg_neg]
    have := norm_sub_norm_le (cexp (↑π * I * x)) (cexp (-(↑π * I * x)))
    rw [norm_exp_piI, norm_exp_neg_piI] at this
    linarith

theorem one_le_norm_rsD {x : ℂ} (h : 1 ≤ |x.im|) : 1 ≤ ‖rsD x‖ := by
  have h1 := norm_rsD_ge x
  have hp : π ≤ π * |x.im| := by nlinarith [Real.pi_pos]
  have h2 : Real.exp π ≤ Real.exp (π * |x.im|) := Real.exp_le_exp.mpr hp
  have h3 : Real.exp (-(π * |x.im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, abs_nonneg x.im]
  have h4 : π + 1 ≤ Real.exp π := Real.add_one_le_exp π
  have h5 : 3 < π := Real.pi_gt_three
  linarith

theorem norm_rsG_le_of_im {x : ℂ} (h : 1 ≤ |x.im|) :
    ‖rsG x‖ ≤ Real.exp (-(2 * π * x.re * x.im)) := by
  unfold rsG
  rw [norm_div, norm_exp_piI_sq]
  have h1 := one_le_norm_rsD h
  exact div_le_self (Real.exp_pos _).le h1











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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The kernels and their algebra -/



























/-! ## 2. Norm bounds -/






















theorem solution {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) (h : 1 ≤ |x.im|) :
    ‖rsG x‖ ≤ Real.exp (-(2 * π) * x.im ^ 2 + 2 * π * (|c₁| + |c₂|) * |x.im|) := by
  refine (norm_rsG_le_of_im h).trans (Real.exp_le_exp.mpr ?_)
  have hd : |x.re - x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have key : x.re * x.im = x.im ^ 2 + (x.re - x.im) * x.im := by ring
  have h2 : -((x.re - x.im) * x.im) ≤ (|c₁| + |c₂|) * |x.im| := by
    calc -((x.re - x.im) * x.im) ≤ |(x.re - x.im) * x.im| := neg_le_abs _
      _ = |x.re - x.im| * |x.im| := abs_mul _ _
      _ ≤ (|c₁| + |c₂|) * |x.im| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hpi := Real.pi_pos
  nlinarith
