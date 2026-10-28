-- Prove2me | solution 1 for RSInt.gauss_fourier_dn
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:51:50.687514+00:00
-- url     : https://prove2.me/submissions/e9a61162-793c-4bb7-8b1c-d29a9f076474

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
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

/-  RS_C0.lean -- lane RS, brick B3 (the Riemann-Siegel remainder), part 1: RIEMANN'S Psi.
    Mathlib-only (imports `RS_B2`).

    The main term of the Riemann-Siegel remainder is the Mordell integral with Gaussian e^{2 pi i w^2}
    (tau = 2):
        rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / (e^{i pi (p+w)} - e^{-i pi (p+w)})),   0 < p < 1.
    Its value is not elementary, but the combination that enters Z(t) is:

        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p) = Psi(p)   (Gabcke's C0).

    Proof (no residue theorem): write e^{i pi w^2} as a Gaussian Fourier integral along the (1-i)
    line, swap the two line integrals (Fubini), evaluate the inner one by the tau = 1 Mordell closed
    form (RS_Kernel), split the outer one into a tau = -1 Mordell integral (closed form by conjugation
    and one pole crossing) and a tau = -2 integral that is the conjugate of rsJ itself (symmetry
    rsJ(1-p) = rsJ(p)).  This gives rsJ + e^{i pi/4} conj(rsJ) = elementary, whose real part after the
    phase e^{-i pi/8} is Psi.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Linearity for `lineDn`, translations -/









/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/

theorem half_cpow_half_mul_sub : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 - I) = cexp (-(↑π / 4 * I)) := by
  have h1 : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have : ((1 / 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (((1 / 2 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
      (ofReal_cpow (by norm_num) _).symm
    push_cast at this
    rw [this]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_one]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h1, show -(↑π / 4 * I) = (-(↑π / 4 : ℂ)) * I by ring, Complex.exp_mul_I,
    ← ofReal_ofNat 4, ← ofReal_div, ← ofReal_neg, ← ofReal_cos, ← ofReal_sin, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring_nf



/-! ## 3. The tau = 2 Mordell integral and its symmetry -/















/-! ## 4. Fubini: rsJ as an iterated integral -/



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/



/-! ## 6. The outer integral splits into T1 - T2 -/









/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/







/-! ## 8. Riemann's Psi -/



end RSInt

end

/-  RS_C0.lean -- lane RS, brick B3 (the Riemann-Siegel remainder), part 1: RIEMANN'S Psi.
    Mathlib-only (imports `RS_B2`).

    The main term of the Riemann-Siegel remainder is the Mordell integral with Gaussian e^{2 pi i w^2}
    (tau = 2):
        rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / (e^{i pi (p+w)} - e^{-i pi (p+w)})),   0 < p < 1.
    Its value is not elementary, but the combination that enters Z(t) is:

        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p) = Psi(p)   (Gabcke's C0).

    Proof (no residue theorem): write e^{i pi w^2} as a Gaussian Fourier integral along the (1-i)
    line, swap the two line integrals (Fubini), evaluate the inner one by the tau = 1 Mordell closed
    form (RS_Kernel), split the outer one into a tau = -1 Mordell integral (closed form by conjugation
    and one pole crossing) and a tau = -2 integral that is the conjugate of rsJ itself (symmetry
    rsJ(1-p) = rsJ(p)).  This gives rsJ + e^{i pi/4} conj(rsJ) = elementary, whose real part after the
    phase e^{-i pi/8} is Psi.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Linearity for `lineDn`, translations -/









/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/




theorem solution (w : ℂ) :
    cexp (↑π * I * w ^ 2) =
      cexp (↑π / 4 * I) * lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2) + 2 * ↑π * I * u * w)) := by
  unfold lineDn
  have hpt : ∀ r : ℝ, cexp (-(↑π * I * (((0 : ℝ) : ℂ) + r * (1 - I)) ^ 2) +
      2 * ↑π * I * (((0 : ℝ) : ℂ) + r * (1 - I)) * w) * (1 - I) =
      cexp ((-2 * ↑π) * (r : ℂ) ^ 2 + (2 * ↑π * I * (1 - I) * w) * r + 0) * (1 - I) := by
    intro r
    congr 2
    push_cast
    linear_combination (2 * ↑π * (r : ℂ) ^ 2 - ↑π * I * (r : ℂ) ^ 2) * I_sq
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_mul_const,
    integral_cexp_quadratic (by simp [Real.pi_pos])]
  have hb : (↑π / -(-2 * ↑π) : ℂ) = 1 / 2 := by have := pi_ne_zero'; field_simp
  have hexp : (0 : ℂ) - (2 * ↑π * I * (1 - I) * w) ^ 2 / (4 * (-2 * ↑π)) = ↑π * I * w ^ 2 := by
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (-4 * ↑π * I * w ^ 2 + 2 * ↑π * I ^ 2 * w ^ 2) * I_sq
  rw [hb, hexp]
  have h2 := half_cpow_half_mul_sub
  have h3 : cexp (↑π / 4 * I) * cexp (-(↑π / 4 * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (-cexp (↑π * I * w ^ 2)) * h3 -
    (cexp (↑π / 4 * I) * cexp (↑π * I * w ^ 2)) * h2
