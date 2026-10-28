-- Prove2me | solution 1 for SelfishMiningRuin.ValueFn.equations_39_40
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:33:17.363788+00:00
-- url     : https://prove2.me/submissions/035c24a8-b165-4df3-87f8-5778e4d527a3

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Formula

set_option autoImplicit false

namespace Aux_SMRV3940
open SelfishMiningRuin.ValueFn

noncomputable def Hn (A1 ρ1 : ℝ) (W z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (A1 : ℂ) * (ρ1 : ℂ) ^ n * Complex.exp ((ρ1 : ℂ) * u) + W * z ^ n * Complex.exp (z * u)

lemma hasDerivAt_cexp_lin (w : ℂ) (u : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (w * y)) (w * Complex.exp (w * u)) u := by
  have h := (((hasDerivAt_id u).ofReal_comp).const_mul w).cexp
  refine h.congr_deriv ?_
  simp only [id, Complex.ofReal_one, mul_one]
  ring

lemma hasDerivAt_Hn (A1 ρ1 : ℝ) (W z : ℂ) (n : ℕ) (u : ℝ) :
    HasDerivAt (Hn A1 ρ1 W z n) (Hn A1 ρ1 W z (n + 1) u) u := by
  have h := ((hasDerivAt_cexp_lin (ρ1 : ℂ) u).const_mul ((A1 : ℂ) * (ρ1 : ℂ) ^ n)).add
    ((hasDerivAt_cexp_lin z u).const_mul (W * z ^ n))
  refine h.congr_deriv ?_
  simp only [Hn]
  ring

lemma re_deriv (A1 ρ1 : ℝ) (W z : ℂ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y => (Hn A1 ρ1 W z n y).re) (Hn A1 ρ1 W z (n + 1) u).re u :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_Hn A1 ρ1 W z n u)

lemma lin_id (lam c b t p q u : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p < 1) :
    D6 lam c t p * 1 + D7 lam t p q * (u + Cconst lam c b t p q) -
      D3 lam p q * (u + b + Cconst lam c b t p q) -
      D2 lam t p * (u + 2 * b + Cconst lam c b t p q) - D1 lam c t p * 1 -
      (1+lam*t*(p+2)-lam^2*t^2*(p^2-2*p-1))/(t^3*lam^2*(1-p)*p)*u -
      (2+lam*t*(p+2))*c/(lam^2*t^2*(1-p)*p) = 0 := by
  have hden : Cden lam t p ≠ 0 := by
    unfold Cden
    have h1 : p ^ 2 - 2 * p - 1 < 0 := by nlinarith
    have h2 : lam ^ 2 * t ^ 2 * (p ^ 2 - 2 * p - 1) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) h1
    have h3 : 0 < (p + 2) * lam * t := by positivity
    linarith
  have h1p : (1 - p) ≠ 0 := by linarith
  have hl := hlam.ne'
  have htt := ht.ne'
  have hpp := hp0.ne'
  unfold D6 D7 D3 D2 D1 Cconst
  generalize hX : Cden lam t p = X at hden ⊢
  field_simp
  unfold Cden at hX
  rw [← hX]
  ring

lemma key_complex (lam c b t p q A1 ρ1 : ℝ) (W z : ℂ) (u : ℝ) :
    (D4 lam c p : ℂ) * Hn A1 ρ1 W z 3 u + (D5 lam c t p : ℂ) * Hn A1 ρ1 W z 2 u +
      (D6 lam c t p : ℂ) * Hn A1 ρ1 W z 1 u + (D7 lam t p q : ℂ) * Hn A1 ρ1 W z 0 u -
      (D3 lam p q : ℂ) * Hn A1 ρ1 W z 0 (u + b) - (D2 lam t p : ℂ) * Hn A1 ρ1 W z 0 (u + 2 * b) -
      (D1 lam c t p : ℂ) * Hn A1 ρ1 W z 1 (u + 2 * b) =
    -((A1 : ℂ) * Complex.exp ((ρ1 : ℂ) * u)) * charFun lam c b t p q (ρ1 : ℂ) -
      W * Complex.exp (z * u) * charFun lam c b t p q z := by
  have e1 : ∀ w : ℂ, Complex.exp (w * ((u + b : ℝ) : ℂ)) =
      Complex.exp (w * u) * Complex.exp (w * (b : ℂ)) := by
    intro w; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : ∀ w : ℂ, Complex.exp (w * ((u + 2 * b : ℝ) : ℂ)) =
      Complex.exp (w * u) * Complex.exp (2 * w * (b : ℂ)) := by
    intro w; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [Hn, charFun, e1, e2]
  ring

end Aux_SMRV3940

open SelfishMiningRuin.ValueFn Aux_SMRV3940 in
theorem solution (lam c b t p q rho1 rho2 rho3 A1 A2 A3 : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hroot1 : charFun lam c b t p q (rho1 : ℂ) = 0)
    (hroot2 : charFun lam c b t p q (Complex.mk rho2 rho3) = 0) :
    let F := closedForm lam c b t p q rho1 rho2 rho3 A1 A2 A3
    (∀ u : ℝ, E32 lam c b t p q F u = 0) ∧
    ((F 0 = 0 ∧ deriv F 0 = 0 ∧
      iteratedDeriv 2 F 0 = lam^2*p^2/c^2*F (2*b) + 1/(c*t)) ↔
      System23 lam c b t p q rho1 rho2 rho3 A1 A2 A3) := by
  intro F
  set W : ℂ := Complex.mk A2 (-A3) with hW
  set z : ℂ := Complex.mk rho2 rho3 with hz
  set C := Cconst lam c b t p q with hC
  have hF : F = fun u => (Hn A1 rho1 W z 0 u).re + u + C := by
    funext u
    simp [F, closedForm, Hn, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
      hW, hz, hC]
    ring_nf
  have hdF : deriv F = fun u => (Hn A1 rho1 W z 1 u).re + 1 := by
    funext u
    rw [hF]
    exact (((re_deriv A1 rho1 W z 0 u).add (hasDerivAt_id u)).add_const C).deriv
  have h2F : iteratedDeriv 2 F = fun u => (Hn A1 rho1 W z 2 u).re := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hdF]
    funext u
    exact ((re_deriv A1 rho1 W z 1 u).add_const 1).deriv
  have h3F : iteratedDeriv 3 F = fun u => (Hn A1 rho1 W z 3 u).re := by
    rw [iteratedDeriv_succ, h2F]
    funext u
    exact (re_deriv A1 rho1 W z 2 u).deriv
  refine ⟨?_, ?_⟩
  · intro u
    have hk := congrArg Complex.re (key_complex lam c b t p q A1 rho1 W z u)
    rw [hroot1, hroot2] at hk
    simp only [mul_zero, sub_zero, neg_zero, Complex.zero_re, Complex.sub_re, Complex.add_re,
      Complex.re_ofReal_mul] at hk
    have hl := lin_id lam c b t p q u hlam ht hp0 hp1
    unfold E32
    rw [h3F, h2F, hdF, hF]
    simp only
    rw [← hC] at hl
    linear_combination hk + hl
  · have hF0 : F 0 = A1 + A2 + C := by
      rw [hF]; simp [Hn, hW, hz]
    have hdF0 : deriv F 0 = A1 * rho1 + (A2 * rho2 + A3 * rho3) + 1 := by
      rw [hdF]; simp [Hn, hW, hz, Complex.mul_re]
    have h2F0 : iteratedDeriv 2 F 0 =
        A1 * rho1 ^ 2 + (A2 * (rho2 ^ 2 - rho3 ^ 2) + A3 * (2 * rho2 * rho3)) := by
      rw [h2F]
      simp only [Hn, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Complex.add_re]
      rw [show ((A1 : ℂ) * (rho1 : ℂ) ^ 2).re = A1 * rho1 ^ 2 by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]]
      rw [hW, hz]
      simp only [sq, Complex.mul_re, Complex.mul_im]
      ring
    have hF2b : F (2 * b) = A1 * Real.exp (2 * b * rho1) + Real.exp (2 * b * rho2) *
        (A2 * Real.cos (2 * b * rho3) + A3 * Real.sin (2 * b * rho3)) + 2 * b + C := by
      simp only [F, closedForm, hC]
      rw [show rho1 * (2 * b) = 2 * b * rho1 by ring, show rho2 * (2 * b) = 2 * b * rho2 by ring,
        show rho3 * (2 * b) = 2 * b * rho3 by ring]
    rw [hF0, hdF0, h2F0, hF2b]
    unfold System23 B1 B2 B3
    rw [← hC]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨by linarith, by linarith, ?_⟩
      linear_combination -h2
    · rintro ⟨h0, h1, h2⟩
      refine ⟨by linarith, by linarith, ?_⟩
      linear_combination -h2
