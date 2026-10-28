-- Prove2me | solution 1 for RSInt.rsJ_C0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:26:49.102535+00:00
-- url     : https://prove2.me/submissions/82896e29-b3e2-40dd-9d0c-e86678ab7c5c

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_lineUp_cross
import Theorems.Thm_RSInt_lineUp_mordell
import Theorems.Thm_RSInt_rsJ_outer
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











theorem exp_neg_piI : cexp (-(↑π * I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

theorem rsD_add_one (x : ℂ) : rsD (x + 1) = -rsD x := by
  unfold rsD
  have e1 : cexp (↑π * I * (x + 1)) = -cexp (↑π * I * x) := by
    rw [show ↑π * I * (x + 1) = ↑π * I * x + ↑π * I by ring, Complex.exp_add,
      Complex.exp_pi_mul_I]; ring
  have e2 : cexp (-(↑π * I * (x + 1))) = -cexp (-(↑π * I * x)) := by
    rw [show -(↑π * I * (x + 1)) = -(↑π * I * x) + -(↑π * I) by ring, Complex.exp_add,
      exp_neg_piI]; ring
  rw [e1, e2]; ring





/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/





theorem lineUp_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineUp c (fun x => k * F x) = k * lineUp c F := by
  unfold lineUp; rw [← integral_const_mul]; congr 1; ext v; ring







/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

open ComplexConjugate in
theorem conj_lineUp_pt (c v : ℝ) : conj ((c : ℂ) + v * (1 + I)) = (c : ℂ) + v * (1 - I) := by
  simp only [map_add, map_mul, Complex.conj_ofReal, map_one, Complex.conj_I]; ring

open ComplexConjugate in
theorem lineDn_eq_conj (c : ℝ) (F : ℂ → ℂ) :
    lineDn c F = conj (lineUp c (fun x => conj (F (conj x)))) := by
  unfold lineDn lineUp
  rw [← integral_conj]
  congr 1; ext v
  rw [map_mul, Complex.conj_conj, conj_lineUp_pt]
  congr 1
  simp only [map_add, map_one, Complex.conj_I]; ring

open ComplexConjugate in
theorem conj_rsD_conj (x : ℂ) : conj (rsD (conj x)) = -rsD x := by
  unfold rsD
  rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  ring_nf

open ComplexConjugate in
theorem conj_rsH_conj (x : ℂ) : conj (rsH (conj x)) = -rsG x := by
  unfold rsH rsG
  rw [map_div₀, conj_rsD_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  rw [div_neg]
  ring_nf

open ComplexConjugate in
theorem lineDn_rsH_eq (c : ℝ) (ψ : ℂ → ℂ) :
    lineDn c (fun x => rsH x * ψ x) =
      -conj (lineUp c (fun x => rsG x * conj (ψ (conj x)))) := by
  rw [lineDn_eq_conj, ← map_neg]
  congr 1
  have : (fun x => conj (rsH (conj x) * ψ (conj x))) =
      fun x => (-1) * (rsG x * conj (ψ (conj x))) := by
    ext x; rw [map_mul, conj_rsH_conj]; ring
  rw [this, lineUp_const_mul]; ring

open ComplexConjugate in
theorem conj_mem_dnStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    (conj x).re + (conj x).im ∈ Icc c₁ c₂ := by
  simpa [sub_eq_add_neg] using hx

/-- **Crossing a pole, slope (-1).**  For `n - 1 < c1 < n < c2 < n + 1` and `psi` holomorphic on the
    closed slope-(-1) strip with at most exponential growth:
        lineDn c2 (rsH * psi) = lineDn c1 (rsH * psi) - psi n. -/
theorem lineDn_cross {ψ : ℂ → ℂ} {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1)
    (hψ : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ ψ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineDn c₂ (fun x => rsH x * ψ x) = lineDn c₁ (fun x => rsH x * ψ x) - ψ n := by
  open ComplexConjugate in
  rw [lineDn_rsH_eq, lineDn_rsH_eq]
  have hc := lineUp_cross (φ := fun x => (starRingEnd ℂ) (ψ ((starRingEnd ℂ) x))) h₁ h₁' h₂ h₂'
    (fun x hx => differentiableAt_conj_conj_iff.mpr (hψ _ (conj_mem_dnStrip hx))) (A := A) (B := B)
    (fun x hx => by
      rw [RCLike.norm_conj]
      have := hgrow _ (conj_mem_dnStrip hx)
      rwa [RCLike.norm_conj] at this)
  rw [hc, map_add, Complex.conj_conj, map_intCast]
  ring



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





theorem lineDn_shift (p : ℝ) (H : ℂ → ℂ) : lineDn 0 (fun u => H (u + p)) = lineDn p H := by
  unfold lineDn; congr 1; ext v; congr 2; push_cast; ring

/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/



theorem rsD_one_sub (z : ℂ) : rsD (1 - z) = rsD z := by
  unfold rsD
  rw [show ↑π * I * (1 - z) = ↑π * I + -(↑π * I * z) by ring,
    show -(↑π * I + -(↑π * I * z)) = -(↑π * I) + ↑π * I * z by ring, Complex.exp_add,
    Complex.exp_add, Complex.exp_pi_mul_I, exp_neg_piI]
  ring

theorem rsJ_symm (p : ℝ) : rsJ (1 - p) = rsJ p := by
  unfold rsJ lineUp
  rw [← integral_neg_eq_self]
  congr 1; ext v
  push_cast
  rw [show (1 : ℂ) - ↑p + (0 + -(v : ℂ) * (1 + I)) = 1 - (↑p + (0 + ↑v * (1 + I))) by ring,
    rsD_one_sub]
  ring_nf









/-! ## 4. Fubini: rsJ as an iterated integral -/



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/



/-! ## 6. The outer integral splits into T1 - T2 -/









/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/

theorem T2_eq {p : ℝ} :
    lineDn (-p) (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y) =
      cexp (2 * ↑π * I * p ^ 2) * conj (rsJ p) := by
  rw [← lineDn_shift (-p)]
  have h1 : (fun u => (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y)
      (u + ((-p : ℝ) : ℂ))) =
      fun u => cexp (2 * ↑π * I * p ^ 2) * (cexp (-(2 * ↑π * I * u ^ 2)) / rsD (u - p)) := by
    ext u
    simp only
    rw [show u + ((-p : ℝ) : ℂ) = u - p by push_cast; ring, mul_div_assoc', ← Complex.exp_add]
    congr 2; ring
  rw [h1, lineDn_const_mul, lineDn_eq_conj]
  congr 2
  rw [← rsJ_symm p]
  unfold rsJ
  congr 1; ext x
  have hc : conj x - (p : ℂ) = conj (x - p) := by simp [map_sub]
  rw [map_div₀, ← Complex.exp_conj, hc, conj_rsD_conj,
    show ((1 - p : ℝ) : ℂ) + x = (x - p) + 1 by push_cast; ring, rsD_add_one]
  congr 1
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj,
    map_ofNat]
  congr 1; ring

theorem norm_exp_lin_le (ζ x : ℂ) : ‖cexp (ζ * x)‖ ≤ 1 * Real.exp (‖ζ‖ * ‖x‖) := by
  rw [one_mul]
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_mul]))

theorem T1_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    lineDn (-p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) =
      1 - conj (rsK (1 - p) (↑π * I * (1 - 4 * p))) := by
  have hcross := lineDn_cross (ψ := fun y => cexp (↑π * I * (1 - 4 * p) * y)) (n := 0)
    (c₁ := -p) (c₂ := 1 - p) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) (fun x _ => by fun_prop)
    (A := 1) (B := ‖(↑π * I * (1 - 4 * (p : ℂ)))‖)
    (fun x _ => by
      show ‖cexp (↑π * I * (1 - 4 * (p : ℂ)) * x)‖ ≤
        1 * Real.exp (‖(↑π * I * (1 - 4 * (p : ℂ)))‖ * ‖x‖)
      exact norm_exp_lin_le _ x)
  have h2 : lineDn (1 - p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) =
      -conj (rsK (1 - p) (↑π * I * (1 - 4 * p))) := by
    rw [lineDn_rsH_eq]
    congr 2
    unfold rsK
    congr 1; ext x
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_sub, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_conj]
    ring
  rw [h2] at hcross
  simp only [Int.cast_zero, mul_zero, Complex.exp_zero] at hcross
  linear_combination -hcross

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









/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/







/-! ## 8. Riemann's Psi -/


theorem solution {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hcos : Real.cos (2 * π * p) ≠ 0) :
    2 * (cexp (-(↑π / 8 * I)) * rsJ p).re =
      Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p) := by
  -- the basic units
  set a : ℂ := cexp (↑π / 8 * I) with ha
  set b : ℂ := cexp (↑π * I * p) with hb
  set c : ℂ := cexp (↑π * I * p ^ 2) with hc
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  have hb0 : b ≠ 0 := Complex.exp_ne_zero _
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have conj_exp_I : ∀ x : ℝ, conj (cexp (↑x * I)) = (cexp (↑x * I))⁻¹ := by
    intro x
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1; simp [map_mul]
  have hca : conj a = a⁻¹ := by
    have := conj_exp_I (π / 8); push_cast at this; exact this
  have hcb : conj b = b⁻¹ := by
    have := conj_exp_I (π * p); push_cast at this
    rw [hb, show ↑π * I * (p : ℂ) = ↑π * ↑p * I by ring]; exact this
  have hcc : conj c = c⁻¹ := by
    have := conj_exp_I (π * p ^ 2); push_cast at this
    rw [hc, show ↑π * I * (p : ℂ) ^ 2 = ↑π * ↑p ^ 2 * I by ring]; exact this
  have ha8 : a ^ 8 = -1 := by
    rw [ha, ← Complex.exp_nat_mul, show ((8 : ℕ) : ℂ) * (↑π / 8 * I) = ↑π * I by push_cast; ring,
      Complex.exp_pi_mul_I]
  -- the Mordell data at c = 1 - p, zeta = pi i (1 - 4p)
  set ζ : ℂ := ↑π * I * (1 - 4 * p) with hζ
  set K := rsK (1 - p) ζ with hK
  have hM : K * (cexp (-ζ / 2) - cexp (ζ / 2)) = cexp (-ζ / 2) - cexp (I * ζ ^ 2 / (4 * ↑π)) :=
    lineUp_mordell (by linarith) (by linarith) ζ
  have hE1 : cexp (-ζ / 2) = a⁻¹ ^ 4 * b ^ 2 := by
    rw [ha, hb, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      hζ]
    congr 1; push_cast; ring
  have hE2 : cexp (ζ / 2) = a ^ 4 * b⁻¹ ^ 2 := by
    rw [ha, hb, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      hζ]
    congr 1; push_cast; ring
  have hG : cexp (I * ζ ^ 2 / (4 * ↑π)) = a⁻¹ ^ 2 * b ^ 2 * c⁻¹ ^ 4 := by
    rw [ha, hb, hc, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hζ]
    congr 1
    have hpi := pi_ne_zero'
    field_simp
    push_cast
    linear_combination (8 - 64 * (p : ℂ) + 128 * (p : ℂ) ^ 2) * I_sq
  rw [hE1, hE2, hG] at hM
  -- conjugate of the Mordell identity
  have hMc := congrArg conj hM
  simp only [map_mul, map_sub, map_pow, map_inv₀, hca, hcb, hcc, inv_inv] at hMc
  -- the outer relation
  have hout := rsJ_outer hp hp1
  rw [T1_eq hp hp1, T2_eq] at hout
  have hcinv2 : cexp (-(2 * ↑π * I * p ^ 2)) = c⁻¹ ^ 2 := by
    rw [hc, ← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hc2 : cexp (2 * ↑π * I * p ^ 2) = c ^ 2 := by
    rw [hc, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have ha2 : cexp (↑π / 4 * I) = a ^ 2 := by
    rw [ha, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hcinv2, hc2, ha2, ← hK] at hout
  -- X + conj X
  set X := cexp (-(↑π / 8 * I)) * rsJ p with hX
  have hXa : cexp (-(↑π / 8 * I)) = a⁻¹ := by rw [ha, Complex.exp_neg]
  have haa : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  have hcc2 : c⁻¹ ^ 2 * c ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  have hsum : X + conj X = a * c⁻¹ ^ 2 * (1 - conj K) := by
    have hconjX : conj X = a * conj (rsJ p) := by rw [hX, map_mul, hXa, map_inv₀, hca, inv_inv]
    rw [hconjX, hX, hXa]
    linear_combination a⁻¹ * hout + (a * c⁻¹ ^ 2 * (1 - conj K) -
      a * conj (rsJ p) * c⁻¹ ^ 2 * c ^ 2) * haa - (a * conj (rsJ p)) * hcc2
  -- the right-hand side as a function of a, b, c
  have hcosx : ((Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) : ℝ) : ℂ) =
      (c ^ 2 * b⁻¹ ^ 2 * a⁻¹ + c⁻¹ ^ 2 * b ^ 2 * a) / 2 := by
    rw [Complex.ofReal_cos, show Complex.cos _ = (2 * Complex.cos _) / 2 by ring, Complex.two_cos,
      ha, hb, hc]
    rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  have hcosy : ((Real.cos (2 * π * p) : ℝ) : ℂ) = (b ^ 2 + b⁻¹ ^ 2) / 2 := by
    rw [Complex.ofReal_cos, show Complex.cos _ = (2 * Complex.cos _) / 2 by ring, Complex.two_cos,
      hb, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 2 <;> push_cast <;> ring
  have hden : b ^ 2 + b⁻¹ ^ 2 ≠ 0 := by
    intro h; apply hcos
    have : ((Real.cos (2 * π * p) : ℝ) : ℂ) = 0 := by rw [hcosy, h, zero_div]
    exact_mod_cast this
  have hD : a ^ 4 * b⁻¹ ^ 2 - a⁻¹ ^ 4 * b ^ 2 ≠ 0 := by
    intro h; apply hden
    have hab : (a ^ 4 * b⁻¹ ^ 2 - a⁻¹ ^ 4 * b ^ 2) * (a ^ 4 * b ^ 2) = a ^ 8 - b ^ 4 := by
      field_simp
    rw [h, zero_mul, ha8] at hab
    have hb2 : b ^ 2 + b⁻¹ ^ 2 = (b ^ 4 + 1) / b ^ 2 := by field_simp
    rw [hb2, show b ^ 4 + 1 = 0 by linear_combination hab, zero_div]
  -- solve for conj K
  have hKc : conj K = (a ^ 4 * b⁻¹ ^ 2 - a ^ 2 * b⁻¹ ^ 2 * c ^ 4) / (a ^ 4 * b⁻¹ ^ 2 - a⁻¹ ^ 4 * b ^ 2) := by
    rw [eq_div_iff hD]; linear_combination hMc
  -- conclude
  have h1b : 1 + b ^ 4 ≠ 0 := by
    intro h; apply hden
    have hb2 : b ^ 2 + b⁻¹ ^ 2 = (b ^ 4 + 1) / b ^ 2 := by field_simp
    rw [hb2, show b ^ 4 + 1 = 0 by linear_combination h, zero_div]
  have h8b : a ^ 8 - b ^ 4 ≠ 0 := by
    rw [ha8]; intro h; apply h1b; linear_combination -h
  have hfinal : X + conj X =
      ((Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p) : ℝ) : ℂ) := by
    rw [hsum, hKc, Complex.ofReal_div, hcosx, hcosy]
    have hu : (1 + b ^ 4)⁻¹ * (1 + b ^ 4) = 1 := inv_mul_cancel₀ h1b
    field_simp
    linear_combination (c ^ 4 - c ^ 4 * (1 + b ^ 4)⁻¹ - a ^ 2 * b ^ 4 * (1 + b ^ 4)⁻¹) * ha8 +
      (a ^ 2 * b ^ 4 + c ^ 4) * hu
  rw [Complex.add_conj] at hfinal
  exact_mod_cast hfinal
