-- Prove2me | solution 1 for RSInt.lineUp_mordell
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:21:01.472226+00:00
-- url     : https://prove2.me/submissions/2c1f4517-299b-4fe2-be2b-31aec61b90e4

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
import Theorems.Thm_RSInt_lineUp_cross
import Theorems.Thm_RSInt_lineUp_gauss
import Theorems.Thm_RSInt_rsG_add_one
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

















/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/

theorem one_add_I_sq : (1 + I : ℂ) ^ 2 = 2 * I := by
  ring_nf; rw [I_sq]; ring









/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/

theorem lineUp_congr {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ v : ℝ, F (c + v * (1 + I)) = G (c + v * (1 + I))) : lineUp c F = lineUp c G := by
  unfold lineUp; congr 1; ext v; rw [h]



theorem lineUp_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineUp c (fun x => k * F x) = k * lineUp c F := by
  unfold lineUp; rw [← integral_const_mul]; congr 1; ext v; ring

theorem lineUp_add {F G : ℂ → ℂ} {c : ℝ}
    (hF : Integrable (fun v : ℝ => F (c + v * (1 + I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 + I)))) :
    lineUp c (fun x => F x + G x) = lineUp c F + lineUp c G := by
  unfold lineUp
  rw [← integral_add (hF.mul_const _) (hG.mul_const _)]
  congr 1; ext v; ring



theorem lineUp_add_one (c : ℝ) (F : ℂ → ℂ) :
    lineUp (c + 1) F = lineUp c (fun x => F (x + 1)) := by
  unfold lineUp; congr 1; ext v; congr 2; push_cast; ring

/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn





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

theorem fresnel_pt (c : ℝ) (B : ℂ) (v : ℝ) :
    cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2) =
      cexp ((-2 * ↑π) * (v : ℂ) ^ 2 + (2 * ↑π * I * (c + B) * (1 + I)) * v + ↑π * I * (c + B) ^ 2) := by
  congr 1
  linear_combination (↑π * I * (v : ℂ) ^ 2) * one_add_I_sq + (2 * ↑π * (v : ℂ) ^ 2) * I_sq

theorem integrable_fresnel (c : ℝ) (B : ℂ) :
    Integrable (fun v : ℝ => cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2)) := by
  have := integrable_cexp_quadratic' (b := -2 * ↑π) (by simp [Real.pi_pos])
    (2 * ↑π * I * (c + B) * (1 + I)) (↑π * I * (c + B) ^ 2)
  refine this.congr (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [fresnel_pt]

theorem gauss_pt (y x : ℂ) :
    cexp (↑π * I * (x ^ 2 + x) - x * y) =
      cexp (↑π * I * (x + (1 / 2 + I * y / (2 * ↑π))) ^ 2) *
        cexp (-(↑π * I * (1 / 2 + I * y / (2 * ↑π)) ^ 2)) := by
  rw [← Complex.exp_add]
  congr 1
  have hpi := pi_ne_zero'
  field_simp
  linear_combination (-(4 * ↑π * x * y)) * I_sq

theorem integrable_lineUp_gauss (c : ℝ) (y : ℂ) :
    Integrable (fun v : ℝ => cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I)))
      - ((c : ℂ) + v * (1 + I)) * y)) := by
  have := (integrable_fresnel c (1 / 2 + I * y / (2 * ↑π))).mul_const
    (cexp (-(↑π * I * (1 / 2 + I * y / (2 * ↑π)) ^ 2)))
  refine this.congr (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [gauss_pt]

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























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/


theorem solution {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (y : ℂ) :
    lineUp c (fun x => rsG x * cexp (-(x * y))) * (cexp (-y / 2) - cexp (y / 2)) =
      cexp (-y / 2) - cexp (I * y ^ 2 / (4 * ↑π)) := by
  set K := lineUp c (fun x => rsG x * cexp (-(x * y))) with hK
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ c :=
    notInt_of_Ioo (n := 0) (by simpa using hc) (by simpa using hc1)
  have hgrow : ∀ x : ℂ, ‖cexp (-(x * y))‖ ≤ 1 * Real.exp (‖y‖ * ‖x‖) := by
    intro x; rw [one_mul]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_neg, norm_mul, mul_comm]
  have hcross := lineUp_cross (φ := fun x => cexp (-(x * y))) (n := 1) (c₁ := c) (c₂ := c + 1)
    (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (fun x _ => by fun_prop) (A := 1) (B := ‖y‖) (fun x _ => hgrow x)
  have hi1 : Integrable (fun v : ℝ => rsG (c + v * (1 + I)) * cexp (-((c + v * (1 + I)) * y))) :=
    integrable_lineUp_rsG_mul (φ := fun x => cexp (-(x * y))) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcl
      (fun x _ => by fun_prop) (A := 1) (B := ‖y‖) (fun x _ => hgrow x)
  have htr : lineUp (c + 1) (fun x => rsG x * cexp (-(x * y))) =
      cexp (-y) * K + cexp (-y) * cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) := by
    rw [lineUp_add_one]
    have h1 : lineUp c (fun x => rsG (x + 1) * cexp (-((x + 1) * y))) =
        lineUp c (fun x => cexp (-y) * (rsG x * cexp (-(x * y))) +
          cexp (-y) * cexp (↑π * I * (x ^ 2 + x) - x * y)) := by
      refine lineUp_congr fun v => ?_
      rw [rsG_add_one _ (rsD_ne_zero_of_ne (lineUp_pt_ne_int hcl v))]
      have e1 : cexp (-(((c : ℂ) + v * (1 + I) + 1) * y)) =
          cexp (-y) * cexp (-(((c : ℂ) + v * (1 + I)) * y)) := by
        rw [← Complex.exp_add]; ring_nf
      have e2 : cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I)))) *
          cexp (-(((c : ℂ) + v * (1 + I)) * y)) =
          cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I))) -
            ((c : ℂ) + v * (1 + I)) * y) := by
        rw [← Complex.exp_add]; ring_nf
      rw [e1, ← e2]; ring
    rw [h1, lineUp_add (hi1.const_mul _) ((integrable_lineUp_gauss c y).const_mul _),
      lineUp_const_mul, lineUp_const_mul, lineUp_gauss]
  have h : cexp (-y) * K + cexp (-y) * cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) = K + cexp (-y) := by
    rw [← htr, hcross, Int.cast_one, one_mul]
  have hEE : cexp (-y) = cexp (-y / 2) * cexp (-y / 2) := by
    rw [← Complex.exp_add]; ring_nf
  have hEG : cexp (-y) * cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) =
      cexp (-y / 2) * cexp (I * y ^ 2 / (4 * ↑π)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have hE : cexp (-y / 2) * cexp (y / 2) = 1 := by
    rw [← Complex.exp_add, show -y / 2 + y / 2 = 0 by ring, Complex.exp_zero]
  rw [hEG, hEE] at h
  linear_combination cexp (y / 2) * h -
    (cexp (-y / 2) * K + cexp (I * y ^ 2 / (4 * ↑π)) - cexp (-y / 2)) * hE
