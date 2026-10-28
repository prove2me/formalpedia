-- Prove2me | solution 1 for RSInt.norm_rsG_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:01:37.450517+00:00
-- url     : https://prove2.me/submissions/45925af5-6027-4cfe-958c-3971c4f47e85

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_norm_rsG_le
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

















/-- On the slanted strip `c1 <= Re x - Im x <= c2`, `‖x‖ <= 2 |Im x| + D`, `D = |c1| + |c2|`. -/
theorem norm_le_of_upStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    ‖x‖ ≤ 2 * |x.im| + (|c₁| + |c₂|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im x
  have hd : |x.re - x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have h2 : |x.re| ≤ |x.im| + |x.re - x.im| := by
    calc |x.re| = |x.im + (x.re - x.im)| := by ring_nf
      _ ≤ |x.im| + |x.re - x.im| := abs_add_le _ _
  linarith







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

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/




















theorem solution {φ : ℂ → ℂ} {c₁ c₂ A B : ℝ} {x : ℂ} (hx : x.re - x.im ∈ Icc c₁ c₂)
    (h1 : 1 ≤ |x.im|) (hφ : ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    ‖rsG x * φ x‖ ≤ (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
      Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by
  have hG := norm_rsG_le hx h1
  have hn := norm_le_of_upStrip hx
  have hφ' : ‖φ x‖ ≤ |A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|))) := by
    refine hφ.trans ?_
    calc A * Real.exp (B * ‖x‖) ≤ |A| * Real.exp (B * ‖x‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
      _ ≤ |A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
          apply Real.exp_le_exp.mpr
          calc B * ‖x‖ ≤ |B| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _)
            _ ≤ |B| * (2 * |x.im| + (|c₁| + |c₂|)) :=
                mul_le_mul_of_nonneg_left hn (abs_nonneg B)
  rw [norm_mul]
  calc ‖rsG x‖ * ‖φ x‖ ≤ Real.exp (-(2 * π) * x.im ^ 2 + 2 * π * (|c₁| + |c₂|) * |x.im|) *
        (|A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|)))) :=
        mul_le_mul hG hφ' (norm_nonneg _) (Real.exp_pos _).le
    _ = (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
        Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by
        have e : ∀ p q : ℝ, Real.exp p * (|A| * Real.exp q) = |A| * Real.exp (p + q) := by
          intro p q; rw [Real.exp_add]; ring
        have e' : ∀ p q : ℝ, |A| * Real.exp p * Real.exp q = |A| * Real.exp (p + q) := by
          intro p q; rw [Real.exp_add]; ring
        rw [e, e']; congr 2; ring
