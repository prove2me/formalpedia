-- Prove2me | solution 1 for QSVT19.Main.corollary_10
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T21:18:17.797103+00:00
-- url     : https://prove2.me/submissions/c8975398-77c2-4725-a331-2227937e844f

import Definitions.Def_QSVT19_Main_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorems.Thm_QSVT19_Main_theorem_5

noncomputable section
open Polynomial QAlgorithms
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTReq
abbrev cj (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)
def normal (P Q : ℂ[X]) : Prop :=
  P * cj P + (1 - X ^ 2) * (Q * cj Q) = 1
lemma real_ext {P Q : ℂ[X]} (h : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    P.eval (x : ℂ) = Q.eval (x : ℂ)) : P = Q := by
  apply eq_of_infinite_eval_eq
  exact ((Set.Ioo_infinite (by norm_num : (-1:ℝ)<1)).image
    Complex.ofReal_injective.injOn).mono (by
      rintro _ ⟨x,hx,rfl⟩; exact h x hx)

lemma cj_eval (P : ℂ[X]) (x : ℝ) : (cj P).eval (x : ℂ) = conj (P.eval (x : ℂ)) := by
  simpa only [cj, Polynomial.eval_map, Complex.conj_ofReal] using (Polynomial.eval₂_at_apply (p := P) (starRingEnd ℂ) (x : ℂ))

lemma norm_eval (P : ℂ[X]) (x : ℝ) :
    (P * cj P).eval (x : ℂ) = (‖P.eval (x : ℂ)‖ ^ 2 : ℝ) := by
  simp only [eval_mul, cj_eval, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma normal_iff (P Q : ℂ[X]) : normal P Q ↔
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖P.eval (x : ℂ)‖ ^ 2 + (1-x^2)*‖Q.eval (x : ℂ)‖ ^ 2 = 1 := by
  constructor
  · intro h x _
    have e := congrArg (Polynomial.eval (x:ℂ)) h
    simp only [eval_one] at e
    simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, cj_eval,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at e
    exact_mod_cast e
  · intro h
    apply real_ext
    intro x hx
    simp only [eval_one]
    have e : ((‖P.eval (x:ℂ)‖^2 + (1-x^2)*‖Q.eval (x:ℂ)‖^2 : ℝ):ℂ)=1 :=
      by exact_mod_cast h x ⟨hx.1.le,hx.2.le⟩
    simpa only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, cj_eval,
      mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using e


lemma parity_eval {P : ℂ[X]} {k : ℕ} (hp : HasParity P k) (z : ℂ) :
    P.eval (-z) = (-1:ℂ)^k * P.eval z := by
  have h := congrArg (Polynomial.eval z) hp
  simpa only [eval_comp,eval_neg,eval_X,eval_smul,smul_eq_mul] using h
lemma cj_eval_any (P : ℂ[X]) (z : ℂ) : (cj P).eval z = conj (P.eval (conj z)) := by
  simpa [cj,eval_map] using
    Polynomial.eval₂_at_apply (p := P) (starRingEnd ℂ) (conj z)
lemma normal_real (P Q : ℂ[X]) (hn : normal P Q) (x : ℝ) :
    ‖P.eval (x:ℂ)‖^2+(1-x^2)*‖Q.eval (x:ℂ)‖^2=1 := by
  have h := congrArg (Polynomial.eval (x:ℂ)) hn
  simp only [eval_one] at h
  simp only [eval_add,eval_mul,eval_sub,eval_one,eval_pow,eval_X,cj_eval,
    Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h
lemma pair_conditions (k : ℕ) (P Q : ℂ[X]) (h : QSVT19.Main.IsQSPPair k P Q) :
    (∀ x ∈ Set.Icc (-1:ℝ) 1, ‖P.eval (x:ℂ)‖ ≤ 1) ∧
    (∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x:ℂ)‖) ∧
    (Even k → ∀ x : ℝ, (1:ℂ) ≤ P.eval (Complex.I*x)*(P.map (starRingEnd ℂ)).eval (Complex.I*x)) := by
  have hn : normal P Q := (normal_iff P Q).mpr h.2.2
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hw : 0 ≤ 1-x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ 1+x by linarith [hx.1])]
    have hh := h.2.2 x hx
    nlinarith [mul_nonneg hw (sq_nonneg ‖Q.eval (x:ℂ)‖),norm_nonneg (P.eval (x:ℂ))]
  · intro x hx
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_abs x,sq_nonneg (|x|-1)]
    have hh := normal_real P Q hn x
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg ‖Q.eval (x:ℂ)‖),norm_nonneg (P.eval (x:ℂ))]
  · intro hk x
    have hpk : (-1:ℂ)^k = 1 := hk.neg_one_pow
    have hqk : (-1:ℂ)^(k+1) = -1 := by rw [pow_succ,hpk];ring
    have hz : conj (Complex.I*x) = -(Complex.I*x) := by simp
    have hp : (cj P).eval (Complex.I*x) = conj (P.eval (Complex.I*x)) := by
      rw [cj_eval_any,hz,parity_eval h.2.1.1,hpk,one_mul]
    have hq : (cj Q).eval (Complex.I*x) = -conj (Q.eval (Complex.I*x)) := by
      rw [cj_eval_any,hz,parity_eval h.2.1.2,hqk,neg_one_mul,map_neg]
    have hpN : P.eval (Complex.I*x)*(cj P).eval (Complex.I*x) =
        ((‖P.eval (Complex.I*x)‖^2 : ℝ) : ℂ) := by rw [hp,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    have hqN : Q.eval (Complex.I*x)*(cj Q).eval (Complex.I*x) =
        -((‖Q.eval (Complex.I*x)‖^2 : ℝ) : ℂ) := by rw [hq,mul_neg,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    have hh := congrArg (Polynomial.eval (Complex.I*x)) hn
    change (P*(cj P)+(1-X^2)*(Q*(cj Q))).eval (Complex.I*x) = (1:ℂ[X]).eval (Complex.I*x) at hh
    simp only [eval_add,eval_mul,eval_sub,eval_one,eval_pow,eval_X] at hh
    rw [hpN,hqN] at hh
    have hix : (Complex.I*(x:ℂ))^2 = -(x^2:ℝ) := by simp [mul_pow,Complex.I_sq]
    rw [hix] at hh
    have hr : ‖P.eval (Complex.I*x)‖^2-(1+x^2)*‖Q.eval (Complex.I*x)‖^2=1 := by
      have hr' : ‖P.eval (Complex.I*x)‖^2+(1- -x^2)*(-‖Q.eval (Complex.I*x)‖^2)=1 := by exact_mod_cast hh
      nlinarith only [hr']
    change (1:ℂ) ≤ P.eval (Complex.I*x)*(cj P).eval (Complex.I*x)
    rw [hpN]
    norm_cast
    nlinarith [mul_nonneg (show 0 ≤ 1+x^2 by positivity) (sq_nonneg ‖Q.eval (Complex.I*x)‖)]
end QSVTReq

noncomputable section
open Polynomial QAlgorithms QSVT19.Main
set_option autoImplicit false
lemma cor10_checked (d : ℕ) (hd : 1 ≤ d) (PR : ℝ[X]) (hdeg : PR.natDegree = d)
    (hpar : HasParity (PR.map Complex.ofRealHom) d)
    (hbd : ∀ x ∈ Set.Icc (-1:ℝ) 1, |PR.eval x| ≤ 1) :
    ∃ P : ℂ[X], RePartEq P PR ∧ Cor8Requirements d P := by
  have hr : ((PR.degree ≤ d ∧ (0:ℝ[X]).degree < d) ∧
      (HasParity (PR.map Complex.ofRealHom) d ∧ HasParity ((0:ℝ[X]).map Complex.ofRealHom) (d+1)) ∧
      ∀ x ∈ Set.Icc (-1:ℝ) 1, PR.eval x^2+(1-x^2)*(0:ℝ[X]).eval x^2 ≤ 1) := by
    refine ⟨⟨natDegree_le_iff_degree_le.mp hdeg.le,WithBot.bot_lt_coe d⟩,⟨hpar,by simp [HasParity]⟩,?_⟩
    intro x hx
    simp only [eval_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,add_zero]
    have hh := mul_nonneg (sub_nonneg.mpr (hbd x hx)) (show 0 ≤ 1+|PR.eval x| by positivity)
    nlinarith [sq_abs (PR.eval x)]
  obtain ⟨P,Q,hpair,hRe,_⟩ := (QSVT19.Main.theorem_5 d PR 0).mpr hr
  have hPdeg : P.natDegree = d := by
    apply le_antisymm (natDegree_le_iff_degree_le.mpr hpair.1.1)
    have hdegR : PR.degree ≤ P.degree := by
      apply (degree_le_iff_coeff_zero _ _).mpr
      intro j hj
      rw [← hRe j,coeff_eq_zero_of_degree_lt hj]
      rfl
    have hh := natDegree_le_natDegree hdegR
    rw [hdeg] at hh
    exact hh
  have hc := QSVTReq.pair_conditions d P Q hpair
  exact ⟨P,hRe,hPdeg,hpair.2.1.1,hc⟩

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 10, p. 14: "Let P_ℜ(x) ∈ R[x] be a degree-d polynomial for some d ≥ 1, such
that • P_ℜ has parity-(d mod 2), and • for all x ∈ [−1, 1]: |P_ℜ(x)| ≤ 1.
Then there exists P ∈ C[x] that satisfies the requirements of Corollary 8."

**Formalization Note.** The printed sentence omits `ℜ[P] = P_ℜ`, without which the claim is
trivial (the Chebyshev polynomial `T_d` satisfies the requirements of Corollary 8, by Lemma 9).
The intended claim, used in the proof of Corollary 18 (p. 19: "By Corollary 10 we can find a
Φ ∈ R^n such that ℜ[P] = P_ℜ") and implicit in Corollary 10's own "Moreover" clause, is stated:
`∃ P, ℜ[P] = P_ℜ` and `P` meets Corollary 8's requirements. "degree-d" is `natDegree = d`; the
parity of the real polynomial is that of its image in `ℂ[X]`. The "Moreover" clause (classical
running time) is not part of this statement. -/
theorem solution (d : ℕ) (hd : 1 ≤ d) (PR : ℝ[X]) (hdeg : PR.natDegree = d) (hpar : QAlgorithms.HasParity (PR.map Complex.ofRealHom) d) (hbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |PR.eval x| ≤ 1) :
    ∃ P : ℂ[X], RePartEq P PR ∧ Cor8Requirements d P := by
  exact cor10_checked d hd PR hdeg hpar hbd