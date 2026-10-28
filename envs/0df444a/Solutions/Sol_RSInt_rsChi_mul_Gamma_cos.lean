-- Prove2me | solution 1 for RSInt.rsChi_mul_Gamma_cos
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:04:08.00103+00:00
-- url     : https://prove2.me/submissions/5cfefe84-226c-4965-8743-b4feb606b1a9

import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
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











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



end RSInt

end

/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/







/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/



















/-! ## 3. The chi factor -/






theorem solution {s : ℂ} (hs : 0 < s.re) (hcos : Complex.cos (↑π * s / 2) ≠ 0) :
    rsChi s * Gamma s * (2 * Complex.cos (↑π * s / 2)) = (2 * ↑π) ^ s := by
  have hGb : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGh : Gamma (s / 2 + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hdup := Complex.Gamma_mul_Gamma_add_half (s / 2)
  rw [show 2 * (s / 2) = s by ring] at hdup
  have href := Complex.Gamma_mul_Gamma_one_sub ((1 - s) / 2)
  rw [show 1 - (1 - s) / 2 = s / 2 + 1 / 2 by ring,
    show (↑π : ℂ) * ((1 - s) / 2) = ↑π / 2 - ↑π * s / 2 by ring, Complex.sin_pi_div_two_sub] at href
  have hpi0 := pi_ne_zero'
  set Q : ℂ := (↑π : ℂ) ^ (1 / 2 : ℂ) with hQ
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) = Q := by
    rw [hQ, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  rw [hsqrt] at hdup
  set P : ℂ := (↑π : ℂ) ^ (s - 1 / 2) with hP
  set T : ℂ := (2 : ℂ) ^ (1 - s) with hT
  have hQ0 : Q ≠ 0 := by rw [hQ, Ne, Complex.cpow_eq_zero_iff]; exact fun h => hpi0 h.1
  have hT0 : T ≠ 0 := by rw [hT, Ne, Complex.cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
  have hPQ : P * Q = (↑π : ℂ) ^ s := by
    rw [hP, hQ, ← Complex.cpow_add _ _ hpi0]; congr 1; ring
  have hQQ : Q * Q = ↑π := by
    rw [hQ, ← Complex.cpow_add _ _ hpi0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.cpow_one]
  have hT2 : T * (2 : ℂ) ^ s = 2 := by
    rw [hT, ← Complex.cpow_add _ _ two_ne_zero, show 1 - s + s = 1 by ring, Complex.cpow_one]
  have h2pi : (2 * ↑π : ℂ) ^ s = (2 : ℂ) ^ s * (↑π : ℂ) ^ s := by
    have := Complex.mul_cpow_ofReal_nonneg (a := 2) (b := π) (by norm_num) Real.pi_pos.le s
    push_cast at this; exact this
  -- Gamma s from the duplication formula
  have hGs : Gamma s = Gamma (s / 2) * Gamma (s / 2 + 1 / 2) / (T * Q) := by
    rw [eq_div_iff (mul_ne_zero hT0 hQ0), hdup]; ring
  -- Gamma((1-s)/2) Gamma(s/2 + 1/2) = pi / cos
  unfold rsChi
  rw [← hP, hGs, h2pi, ← hPQ]
  have key : Gamma ((1 - s) / 2) * Gamma (s / 2 + 1 / 2) * Complex.cos (↑π * s / 2) = ↑π := by
    rw [href]; field_simp
  calc P * Gamma ((1 - s) / 2) * (Gamma (s / 2))⁻¹ *
        (Gamma (s / 2) * Gamma (s / 2 + 1 / 2) / (T * Q)) * (2 * Complex.cos (↑π * s / 2))
      = 2 * P * (Gamma ((1 - s) / 2) * Gamma (s / 2 + 1 / 2) * Complex.cos (↑π * s / 2)) /
          (T * Q) := by field_simp
    _ = 2 * P * (Q * Q) / (T * Q) := by rw [key, hQQ]
    _ = 2 * P * Q / T := by field_simp
    _ = T * (2 : ℂ) ^ s * P * Q / T := by rw [hT2]
    _ = (2 : ℂ) ^ s * (P * Q) := by field_simp
