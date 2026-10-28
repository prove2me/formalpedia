-- Prove2me | solution 1 for RSInt.differentiable_rsB
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:01:00.246499+00:00
-- url     : https://prove2.me/submissions/aace2e14-e3a5-42b6-b104-5c308f73b210

import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_differentiable_integral_cpow
import Theorems.Thm_RSInt_norm_rsH_le
/-  RS_Strip.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 1:
    contour tools.

    Mathlib-only (no corpus import), so the file can serve the dbn island's M5 layer L6 as well.

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integrable_exp_quad`, `integrable_of_continuous_of_tail` : integrability of a continuous
        function from a Gaussian-type tail bound `C exp(-a v^2 + b |v|)`.
      * `strip_integral_eq` : Cauchy's theorem on a HORIZONTAL STRIP y1 <= Im z <= y2 with decay at
        both ends: the integrals along the two edges agree.  (Mathlib's rectangle theorem
        `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` plus two limits.)
      * `lineUp c F`, `lineDn c F` : the oriented integrals along the slanted lines through the real
        point `c` with directions `1 + I` (slope +1) and `1 - I` (slope -1).
      * `lineUp_eq_of_strip`, `lineDn_eq_of_strip` : line independence -- the integral along the line
        through `c1` equals the one through `c2` when `F` is continuous on the closed slanted strip,
        holomorphic inside, and tends to 0 at infinity in the strip.

    conjecture1_proved = False.  Contour-integration infrastructure; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RSInt

/-! ## 1. Integrability from a Gaussian tail -/







/-! ## 2. Cauchy's theorem on a horizontal strip -/



/-! ## 3. Slanted lines -/





















theorem norm_one_sub_I : ‖(1 - I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num





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



theorem differentiableAt_rsH {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsH x := by
  unfold rsH
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (-(↑π * I * x ^ 2)))) x).div
    (differentiable_rsD x) h



theorem lineDn_pt_ne_int {c : ℝ} (hc : ∀ m : ℤ, (m : ℝ) ≠ c) (v : ℝ) (n : ℤ) :
    (c : ℂ) + v * (1 - I) ≠ n := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre
  exact hc n (by linarith)



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

namespace RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/







/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/



theorem norm_ge_half_of_dnLine {c v : ℝ} : |c| / 2 ≤ ‖(c : ℂ) + v * (1 - I)‖ := by
  have h1 := Complex.abs_re_le_norm ((c : ℂ) + v * (1 - I))
  have h2 := Complex.abs_im_le_norm ((c : ℂ) + v * (1 - I))
  simp at h1 h2
  have : |c| ≤ |c + v| + |v| := by
    calc |c| = |(c + v) + (-v)| := by ring_nf
      _ ≤ |c + v| + |-v| := abs_add_le _ _
      _ = |c + v| + |v| := by rw [abs_neg]
  linarith



theorem norm_le_of_dnLine (c v : ℝ) : ‖(c : ℂ) + v * (1 - I)‖ ≤ |c| + 2 * |v| := by
  have h := norm_add_le (c : ℂ) (v * (1 - I))
  rw [norm_mul, Complex.norm_real, norm_one_sub_I, Real.norm_eq_abs] at h
  have : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : |v| * Real.sqrt 2 ≤ 2 * |v| := by nlinarith [abs_nonneg v]
  simp at h
  linarith



theorem dnLine_mem_slitPlane {c : ℝ} (hc : 0 < c) (v : ℝ) : (c : ℂ) + v * (1 - I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne v 0 with rfl | hv
  · left; simpa using hc
  · right; simpa using hv

theorem continuous_rsH_line {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Continuous (fun v : ℝ => rsH ((c : ℂ) + v * (1 - I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have h1 : ContinuousAt rsH ((c : ℂ) + v * (1 - I)) :=
    (differentiableAt_rsH (rsD_ne_zero_of_ne (lineDn_pt_ne_int hcl v))).continuousAt
  have h2 : ContinuousAt (fun v : ℝ => (c : ℂ) + v * (1 - I)) v := by fun_prop
  exact ContinuousAt.comp (g := rsH) (f := fun v : ℝ => (c : ℂ) + v * (1 - I)) h1 h2





/-! ## 3. The chi factor -/















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


















theorem solution {c : ℝ} (hc : 0 < c) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Differentiable ℂ (fun s : ℂ => lineDn c (fun x => rsH x * x ^ (s - 1))) := by
  have hmain := differentiable_integral_cpow (W := fun v => rsH ((c : ℂ) + v * (1 - I)) * (1 - I))
    (X := fun v => (c : ℂ) + v * (1 - I)) ((continuous_rsH_line hcl).mul continuous_const)
    (by fun_prop) (dnLine_mem_slitPlane hc) (m := |c| / 2) (by positivity)
    (fun v => norm_ge_half_of_dnLine) (α := |c|) (β := 2) (fun v => norm_le_of_dnLine c v)
    (C := Real.sqrt 2) (a := 2 * π) (b := 2 * π * (|c| + |c|)) (by positivity) (fun v hv => ?_)
  · have hfun : (fun s : ℂ => lineDn c (fun x => rsH x * x ^ (s - 1))) =
        (fun s : ℂ => ∫ v : ℝ, rsH ((c : ℂ) + v * (1 - I)) * (1 - I) * ((c : ℂ) + v * (1 - I)) ^ s)
          ∘ (fun s : ℂ => s - 1) := by
      ext s; simp only [Function.comp, lineDn]; congr 1; ext v; ring
    rw [hfun]
    exact hmain.comp (differentiable_id.sub_const 1)
  · have hx : ((c : ℂ) + v * (1 - I)).re + ((c : ℂ) + v * (1 - I)).im ∈ Icc c c := by simp
    have h1 : 1 ≤ |((c : ℂ) + v * (1 - I)).im| := by simpa using hv
    have hb := norm_rsH_le hx h1
    rw [norm_mul, norm_one_sub_I]
    rw [show ((c : ℂ) + v * (1 - I)).im = -v by simp, abs_neg, neg_sq] at hb
    calc ‖rsH ((c : ℂ) + v * (1 - I))‖ * Real.sqrt 2
        ≤ Real.exp (-(2 * π) * v ^ 2 + 2 * π * (|c| + |c|) * |v|) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * Real.exp (-(2 * π) * v ^ 2 + 2 * π * (|c| + |c|) * |v|) := by ring
