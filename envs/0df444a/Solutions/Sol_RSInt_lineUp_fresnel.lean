-- Prove2me | solution 1 for RSInt.lineUp_fresnel
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:56:05.704574+00:00
-- url     : https://prove2.me/submissions/4738c949-86f6-4d55-8938-3cae83a0322d

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







theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero



















/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/

theorem one_add_I_sq : (1 + I : ℂ) ^ 2 = 2 * I := by
  ring_nf; rw [I_sq]; ring

theorem half_cpow_half_mul : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 + I) = cexp (↑π / 4 * I) := by
  have h1 : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have : ((1 / 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (((1 / 2 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
      (ofReal_cpow (by norm_num) _).symm
    push_cast at this
    rw [this]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_one]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h1, Complex.exp_mul_I, ← ofReal_ofNat 4, ← ofReal_div, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring







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






theorem solution (c : ℝ) (B : ℂ) :
    lineUp c (fun x => cexp (↑π * I * (x + B) ^ 2)) = cexp (↑π / 4 * I) := by
  unfold lineUp
  set w : ℂ := c + B with hw
  have hpt : ∀ v : ℝ, cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2) =
      cexp ((-2 * ↑π) * (v : ℂ) ^ 2 + (2 * ↑π * I * w * (1 + I)) * v + ↑π * I * w ^ 2) := by
    intro v
    congr 1
    rw [hw]
    linear_combination (↑π * I * (v : ℂ) ^ 2) * one_add_I_sq + (2 * ↑π * (v : ℂ) ^ 2) * I_sq
  simp_rw [hpt]
  rw [integral_mul_const, integral_cexp_quadratic (by simp [Real.pi_pos])]
  have hexp : ↑π * I * w ^ 2 - (2 * ↑π * I * w * (1 + I)) ^ 2 / (4 * (-2 * ↑π)) = 0 := by
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (4 * ↑π * I * w ^ 2 + 2 * ↑π * I ^ 2 * w ^ 2) * I_sq
  rw [hexp, Complex.exp_zero, mul_one]
  have hb : (↑π / -(-2 * ↑π) : ℂ) = 1 / 2 := by field_simp
  rw [hb, half_cpow_half_mul]
