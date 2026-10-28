-- Prove2me | solution 1 for RSInt.rsJ_outer
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:23:02.645277+00:00
-- url     : https://prove2.me/submissions/3e1ef364-1f00-4189-8ebd-c90a81c0f9a8

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_mordell
import Theorems.Thm_RSInt_norm_rsH_mul_le
import Theorems.Thm_RSInt_rsJ_fubini
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



theorem differentiable_rsD : Differentiable ℂ rsD := by
  unfold rsD; fun_prop













/-! ## 2. Norm bounds -/





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









theorem lineDn_pt_im (c v : ℝ) : ((c : ℂ) + v * (1 - I)).im = -v := by simp



theorem integrable_lineDn {F : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re + x.im ∈ Icc c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    Integrable (fun v : ℝ => F (c + v * (1 - I))) := by
  have hmem : ∀ v : ℝ, ((c : ℂ) + v * (1 - I)) ∈ {x : ℂ | x.re + x.im ∈ Icc c₁ c₂} := by
    intro v
    simp only [mem_setOf_eq]
    have e : ((c : ℂ) + v * (1 - I)).re + ((c : ℂ) + v * (1 - I)).im = c := by simp
    rw [e]; exact hc
  refine integrable_of_continuous_of_tail (a := a) (b := b) (C := C) (R := 1)
    (hcont.comp_continuous (by fun_prop) hmem) ha (fun v hv => ?_)
  have := hbound _ (hmem v) (by rw [lineDn_pt_im, abs_neg]; exact hv)
  rwa [lineDn_pt_im, abs_neg, neg_sq] at this









/-! ## 5. Linearity and translation of line integrals -/



theorem lineDn_congr {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ v : ℝ, F (c + v * (1 - I)) = G (c + v * (1 - I))) : lineDn c F = lineDn c G := by
  unfold lineDn; congr 1; ext v; rw [h]

theorem lineUp_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineUp c (fun x => k * F x) = k * lineUp c F := by
  unfold lineUp; rw [← integral_const_mul]; congr 1; ext v; ring







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

theorem lineDn_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineDn c (fun x => k * F x) = k * lineDn c F := by
  unfold lineDn; rw [← integral_const_mul]; congr 1; ext v; ring

theorem lineDn_sub {F G : ℂ → ℂ} {c : ℝ}
    (hF : Integrable (fun v : ℝ => F (c + v * (1 - I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 - I)))) :
    lineDn c (fun x => F x - G x) = lineDn c F - lineDn c G := by
  unfold lineDn
  rw [← integral_sub (hF.mul_const _) (hG.mul_const _)]
  congr 1; ext v; ring

theorem lineUp_shift (p : ℝ) (H : ℂ → ℂ) : lineUp 0 (fun w => H (p + w)) = lineUp p H := by
  unfold lineUp; congr 1; ext v; congr 2; push_cast; ring

theorem lineDn_shift (p : ℝ) (H : ℂ → ℂ) : lineDn 0 (fun u => H (u + p)) = lineDn p H := by
  unfold lineDn; congr 1; ext v; congr 2; push_cast; ring

/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/















/-! ## 4. Fubini: rsJ as an iterated integral -/



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/

theorem inner_mordell {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (u : ℂ) :
    lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w)) *
      rsD (u - p) = cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        (cexp (↑π * I * (u - p)) - cexp (-(↑π * I * (u - p) ^ 2))) := by
  set y : ℂ := 2 * ↑π * I * (p - u) with hy
  have h1 : (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w)) =
      fun w => (fun x => cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        (rsG x * cexp (-(x * y)))) (p + w) := by
    ext w
    simp only [rsG, hy]
    rw [show ∀ A B C D : ℂ, A * (B / C * D) = A * B * D / C from fun A B C D => by ring,
      ← Complex.exp_add, ← Complex.exp_add, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2; ring
  rw [h1, lineUp_shift p (fun x => cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
    (rsG x * cexp (-(x * y)))), lineUp_const_mul]
  have hM := lineUp_mordell hp hp1 y
  have hE1 : cexp (-y / 2) = cexp (↑π * I * (u - p)) := by rw [hy]; congr 1; ring
  have hE2 : cexp (y / 2) = cexp (-(↑π * I * (u - p))) := by rw [hy]; congr 1; ring
  have hG : cexp (I * y ^ 2 / (4 * ↑π)) = cexp (-(↑π * I * (u - p) ^ 2)) := by
    rw [hy]; congr 1
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (4 * ((p : ℂ) - u) ^ 2) * I_sq
  rw [hE1, hE2, hG] at hM
  unfold rsD
  rw [mul_assoc, hM]

/-! ## 6. The outer integral splits into T1 - T2 -/

theorem dnLine_neg_p_ne_int {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (r : ℝ) (n : ℤ) :
    ((0 : ℝ) : ℂ) + r * (1 - I) - p ≠ n := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ -p := notInt_of_Ioo (n := -1) (by push_cast; linarith)
    (by push_cast; linarith)
  have := lineDn_pt_ne_int hcl r n
  intro h; apply this; rw [← h]; push_cast; ring

theorem integrable_T1 (p : ℝ) (c : ℝ) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Integrable (fun v : ℝ => rsH ((c : ℂ) + v * (1 - I)) *
      cexp (↑π * I * (1 - 4 * p) * ((c : ℂ) + v * (1 - I)))) := by
  have hcont : ContinuousOn (fun x => rsH x * cexp (↑π * I * (1 - 4 * p) * x))
      {x : ℂ | x.re + x.im ∈ Icc c c} := by
    intro x hx
    have hxc : x.re + x.im = c := le_antisymm hx.2 hx.1
    have hD : rsD x ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hcl n ?_
      rw [hn] at hxc; simpa using hxc
    exact ((differentiableAt_rsH hD).continuousAt.mul (by fun_prop)).continuousWithinAt
  exact integrable_lineDn (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcont (a := 2 * π) (by positivity)
    (fun x hx h1 => norm_rsH_mul_le (ψ := fun x => cexp (↑π * I * (1 - 4 * p) * x)) hx h1
      (A := 1) (B := ‖(↑π * I * (1 - 4 * p) : ℂ)‖) (by
        rw [one_mul]
        refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_mul]))

theorem integrable_T2 {p : ℝ} (c : ℝ) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) (hcp : c = -p) :
    Integrable (fun v : ℝ => cexp (-(2 * ↑π * I * ((c : ℂ) + v * (1 - I)) ^ 2) -
      4 * ↑π * I * p * ((c : ℂ) + v * (1 - I))) / rsD ((c : ℂ) + v * (1 - I))) := by
  have hcont : ContinuousOn (fun x => cexp (-(2 * ↑π * I * x ^ 2) - 4 * ↑π * I * p * x) / rsD x)
      {x : ℂ | x.re + x.im ∈ Icc c c} := by
    intro x hx
    have hxc : x.re + x.im = c := le_antisymm hx.2 hx.1
    have hD : rsD x ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hcl n ?_
      rw [hn] at hxc; simpa using hxc
    exact ((by fun_prop : Continuous (fun x : ℂ => cexp (-(2 * ↑π * I * x ^ 2) -
      4 * ↑π * I * p * x))).continuousAt.div (differentiable_rsD x).continuousAt hD).continuousWithinAt
  refine integrable_lineDn (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcont (a := 4 * π) (b := 0) (C := 1)
    (by positivity) (fun x hx h1 => ?_)
  have hxc : x.re = -p - x.im := by have := le_antisymm hx.2 hx.1; rw [hcp] at this; linarith
  rw [norm_div, Complex.norm_exp]
  have hre : (-(2 * (π : ℂ) * I * x ^ 2) - 4 * (π : ℂ) * I * p * x).re =
      -(4 * π) * x.im ^ 2 + 0 * |x.im| := by
    simp [pow_two, mul_re, mul_im]; rw [hxc]; ring
  rw [hre, one_mul]
  exact div_le_self (Real.exp_pos _).le (one_le_norm_rsD h1)



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



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/



/-! ## 6. The outer integral splits into T1 - T2 -/








theorem solution {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = cexp (↑π / 4 * I) * (cexp (-(2 * ↑π * I * p ^ 2)) *
      (lineDn (-p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) -
        lineDn (-p) (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y))) := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ -p := notInt_of_Ioo (n := -1) (by push_cast; linarith)
    (by push_cast; linarith)
  set Q : ℂ → ℂ := fun y => cexp (-(2 * ↑π * I * p ^ 2)) *
    (rsH y * cexp (↑π * I * (1 - 4 * p) * y) -
      cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y) with hQ
  rw [rsJ_fubini hp hp1]
  congr 1
  have hstep : lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2)) * lineUp 0 (fun w =>
      cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w))) =
      lineDn 0 (fun u => Q (u + ((-p : ℝ) : ℂ))) := by
    refine lineDn_congr fun r => ?_
    set u : ℂ := ((0 : ℝ) : ℂ) + r * (1 - I) with hu
    have hD : rsD (u - p) ≠ 0 := rsD_ne_zero_of_ne (dnLine_neg_p_ne_int hp hp1 r)
    have hin := inner_mordell hp hp1 u
    have hinner : lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) *
        cexp (2 * ↑π * I * u * w)) = cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
          (cexp (↑π * I * (u - p)) - cexp (-(↑π * I * (u - p) ^ 2))) / rsD (u - p) := by
      rw [eq_div_iff hD]; exact hin
    rw [hinner]
    simp only [hQ, rsH]
    rw [show u + ((-p : ℝ) : ℂ) = u - p by push_cast; ring]
    have e1 : cexp (-(↑π * I * u ^ 2)) * cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        cexp (↑π * I * (u - p)) = cexp (-(2 * ↑π * I * p ^ 2)) * cexp (-(↑π * I * (u - p) ^ 2)) *
          cexp (↑π * I * (1 - 4 * p) * (u - p)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; ring
    have e2 : cexp (-(↑π * I * u ^ 2)) * cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        cexp (-(↑π * I * (u - p) ^ 2)) = cexp (-(2 * ↑π * I * p ^ 2)) *
          cexp (-(2 * ↑π * I * (u - p) ^ 2) - 4 * ↑π * I * p * (u - p)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; ring
    calc cexp (-(↑π * I * u ^ 2)) * (cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
          (cexp (↑π * I * (u - p)) - cexp (-(↑π * I * (u - p) ^ 2))) / rsD (u - p))
        = (cexp (-(↑π * I * u ^ 2)) * cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
            cexp (↑π * I * (u - p)) - cexp (-(↑π * I * u ^ 2)) *
            cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) * cexp (-(↑π * I * (u - p) ^ 2))) /
              rsD (u - p) := by ring
      _ = (cexp (-(2 * ↑π * I * p ^ 2)) * cexp (-(↑π * I * (u - p) ^ 2)) *
            cexp (↑π * I * (1 - 4 * p) * (u - p)) - cexp (-(2 * ↑π * I * p ^ 2)) *
            cexp (-(2 * ↑π * I * (u - p) ^ 2) - 4 * ↑π * I * p * (u - p))) / rsD (u - p) := by
          rw [e1, e2]
      _ = _ := by ring
  rw [hstep, lineDn_shift, hQ, lineDn_const_mul, lineDn_sub (integrable_T1 p (-p) hcl)
    (integrable_T2 (-p) hcl rfl)]
