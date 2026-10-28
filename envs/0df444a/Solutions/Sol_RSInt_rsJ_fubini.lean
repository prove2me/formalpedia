-- Prove2me | solution 1 for RSInt.rsJ_fubini
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:14.623379+00:00
-- url     : https://prove2.me/submissions/636f1549-d8f0-4fbc-ba7f-daa548d4db8a

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_gauss_fourier_dn
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
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













/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













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





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/







/-- A point `p + v (1+i)` with `0 < p < 1` is never an integer. -/
theorem pt_ne_int {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (v : ℝ) (n : ℤ) :
    (p : ℂ) + ((0 : ℝ) + v * (1 + I)) ≠ n := by
  have := lineUp_pt_ne_int (c := p) (notInt_of_Ioo (n := 0) (by simpa using hp)
    (by simpa using hp1)) v n
  simpa using this

theorem continuous_J_integrand {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Continuous (fun v : ℝ => cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I)))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hD : rsD (p + ((0 : ℝ) + v * (1 + I))) ≠ 0 := rsD_ne_zero_of_ne (pt_ne_int hp hp1 v)
  exact ((by fun_prop : Continuous (fun v : ℝ => cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2))).continuousAt).div
    ((differentiable_rsD.continuous.comp (by fun_prop :
      Continuous (fun v : ℝ => (p : ℂ) + ((0 : ℝ) + v * (1 + I))))).continuousAt) hD

theorem norm_J_integrand_le {p : ℝ} (v : ℝ) (hv : 1 ≤ |v|) :
    ‖cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) / rsD (p + ((0 : ℝ) + v * (1 + I)))‖ ≤
      1 * Real.exp (-(2 * π) * v ^ 2 + 0 * |v|) := by
  have h1 : 1 ≤ |((p : ℂ) + ((0 : ℝ) + v * (1 + I))).im| := by simpa using hv
  rw [norm_div, norm_exp_piI_sq]
  have hD := one_le_norm_rsD h1
  have hre : -(2 * π * ((0 : ℝ) + v * (1 + I) : ℂ).re * ((0 : ℝ) + v * (1 + I) : ℂ).im) =
      -(2 * π) * v ^ 2 + 0 * |v| := by simp; ring
  rw [hre, one_mul]
  exact div_le_self (Real.exp_pos _).le hD

theorem integrable_J_integrand {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun v : ℝ => cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I)))) :=
  integrable_of_continuous_of_tail (continuous_J_integrand hp hp1) (a := 2 * π) (b := 0) (C := 1)
    (R := 1) (by positivity) (fun v hv => norm_J_integrand_le v hv)

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





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/















/-! ## 4. Fubini: rsJ as an iterated integral -/

theorem solution {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = cexp (↑π / 4 * I) * lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2)) *
      lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w))) := by
  set F : ℝ → ℝ → ℂ := fun v r =>
    cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) / rsD (p + ((0 : ℝ) + v * (1 + I))) * (1 + I) *
      (cexp (-(↑π * I * ((0 : ℝ) + r * (1 - I) : ℂ) ^ 2) +
        2 * ↑π * I * ((0 : ℝ) + r * (1 - I)) * ((0 : ℝ) + v * (1 + I))) * (1 - I)) with hF
  -- rsJ as the iterated integral ∫ v ∫ r
  have hL : rsJ p = cexp (↑π / 4 * I) * ∫ v : ℝ, ∫ r : ℝ, F v r := by
    unfold rsJ lineUp
    rw [← integral_const_mul]
    congr 1; ext v
    simp only [hF]
    rw [integral_const_mul, ← mul_assoc, ← mul_assoc]
    have hg := gauss_fourier_dn ((0 : ℝ) + v * (1 + I))
    unfold lineDn at hg
    rw [show cexp (2 * ↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) =
      cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) * cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2)
        by rw [← Complex.exp_add]; ring_nf]
    conv_lhs => rw [show ∀ A B C : ℂ, A * B / C * (1 + I) = B / C * (1 + I) * A from
      fun A B C => by ring]
    rw [hg]; ring
  -- integrability of F on the product
  have hf₁ : Integrable (fun v : ℝ => ‖cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I))) * (1 + I)‖) :=
    ((integrable_J_integrand hp hp1).mul_const _).norm
  have hf₂ : Integrable (fun r : ℝ => Real.exp (-(2 * π) * r ^ 2) * ‖(1 - I : ℂ)‖) :=
    (integrable_exp_neg_mul_sq (by positivity)).mul_const _
  have hprod := hf₁.mul_prod hf₂
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous (fun q : ℝ × ℝ => F q.1 q.2)
    simp only [hF]
    have h1 : Continuous (fun q : ℝ × ℝ => cexp (↑π * I * ((0 : ℝ) + q.1 * (1 + I) : ℂ) ^ 2) /
        rsD (p + ((0 : ℝ) + q.1 * (1 + I)))) :=
      (continuous_J_integrand hp hp1).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ => cexp (-(↑π * I * ((0 : ℝ) + q.2 * (1 - I) : ℂ) ^ 2) +
        2 * ↑π * I * ((0 : ℝ) + q.2 * (1 - I)) * ((0 : ℝ) + q.1 * (1 + I)))) := by fun_prop
    exact (h1.mul continuous_const).mul (h2.mul continuous_const)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine hprod.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun q => le_of_eq ?_)
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    congr 3
    simp [pow_two, mul_re, mul_im]
    ring
  rw [hL, integral_integral_swap hint]
  congr 1
  unfold lineDn lineUp
  congr 1; ext r
  simp only [hF]
  rw [← integral_const_mul, ← integral_mul_const]
  congr 1; ext v
  rw [show -(↑π * I * ((0 : ℝ) + r * (1 - I) : ℂ) ^ 2) +
      2 * ↑π * I * ((0 : ℝ) + r * (1 - I)) * ((0 : ℝ) + v * (1 + I)) =
      -(↑π * I * ((0 : ℝ) + r * (1 - I) : ℂ) ^ 2) +
      2 * ↑π * I * ((0 : ℝ) + r * (1 - I)) * ((0 : ℝ) + v * (1 + I)) from rfl, Complex.exp_add]
  ring
