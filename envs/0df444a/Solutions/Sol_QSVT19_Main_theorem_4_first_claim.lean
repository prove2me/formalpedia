-- Prove2me | solution 1 for QSVT19.Main.theorem_4_first_claim
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T22:12:28.797631+00:00
-- url     : https://prove2.me/submissions/c4ba5f31-afaf-4503-988d-940895983abc

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Expand
import Definitions.Def_QSVT19_Main_Setting
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Algebra.Polynomial.Lifts

noncomputable section
open Polynomial QAlgorithms
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTCert
lemma parity_add {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q k) : HasParity (P+Q) k := by
  simpa only [HasParity,add_comp,smul_add] using congrArg₂ (·+·) hP hQ
lemma parity_neg {P : ℂ[X]} {k : ℕ} (h : HasParity P k) : HasParity (-P) k := by
  simpa only [HasParity,neg_comp,smul_neg] using congrArg Neg.neg h
lemma parity_sub {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q k) : HasParity (P-Q) k := by
  simpa only [sub_eq_add_neg] using parity_add hP (parity_neg hQ)
lemma parity_mul {P Q : ℂ[X]} {k l : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q l) : HasParity (P*Q) (k+l) := by
  dsimp [HasParity] at *
  rw [mul_comp,hP,hQ,pow_add,mul_smul_mul_comm]
lemma parity_shift (P : ℂ[X]) (k : ℕ) : HasParity P (k+2) ↔ HasParity P k := by
  simp [HasParity,pow_add]
lemma parity_X : HasParity (X : ℂ[X]) 1 := by simp [HasParity]
lemma parity_gap : HasParity (1-X^2 : ℂ[X]) 0 := by simp [HasParity]
lemma degree_mul_lt_right {P Q : ℝ[X]} {k l : ℕ}
    (hP : P.degree ≤ k) (hQ : Q.degree < l) : (P*Q).degree < (↑(k+l) : WithBot ℕ) := by
  by_cases hp : P = 0
  · simp [hp]
  by_cases hq : Q = 0
  · simp [hq]
  rw [degree_eq_natDegree hp] at hP
  rw [degree_eq_natDegree hq] at hQ
  rw [degree_mul,degree_eq_natDegree hp,degree_eq_natDegree hq]
  exact_mod_cast Nat.add_lt_add_of_le_of_lt (by exact_mod_cast hP) (by exact_mod_cast hQ)
lemma degree_gap_mul {P Q : ℝ[X]} {k l : ℕ}
    (hP : P.degree < k) (hQ : Q.degree < l) :
    ((1-X^2)*P*Q).degree ≤ (↑(k+l) : WithBot ℕ) := by
  by_cases hp : P = 0
  · simp [hp]
  by_cases hq : Q = 0
  · simp [hq]
  have hg : (1-X^2 : ℝ[X]) ≠ 0 := by intro h;have := congrArg (fun p : ℝ[X] => p.coeff 2) h;norm_num [coeff_one] at this
  have hd : (1-X^2 : ℝ[X]).degree = 2 := by compute_degree!
  rw [degree_eq_natDegree hp] at hP
  rw [degree_eq_natDegree hq] at hQ
  rw [degree_mul,degree_mul,hd,degree_eq_natDegree hp,degree_eq_natDegree hq]
  have hk : P.natDegree < k := by exact_mod_cast hP
  have hl : Q.natDegree < l := by exact_mod_cast hQ
  have h : 2 + P.natDegree + Q.natDegree ≤ k+l := by omega
  exact_mod_cast h
lemma certificate_mul (k l : ℕ) (A B C D E F : ℝ[X])
    (hA : A = B^2 + (1-X^2)*C^2) (hD : D = E^2 + (1-X^2)*F^2)
    (hB : B.degree ≤ k) (hC : C.degree < k)
    (hE : E.degree ≤ l) (hF : F.degree < l)
    (hpB : HasParity (B.map Complex.ofRealHom) k)
    (hpC : HasParity (C.map Complex.ofRealHom) (k+1))
    (hpE : HasParity (E.map Complex.ofRealHom) l)
    (hpF : HasParity (F.map Complex.ofRealHom) (l+1)) :
    A*D = (B*E-(1-X^2)*C*F)^2 + (1-X^2)*(B*F+C*E)^2 ∧
      (B*E-(1-X^2)*C*F).degree ≤ (↑(k+l) : WithBot ℕ) ∧ (B*F+C*E).degree < (↑(k+l) : WithBot ℕ) ∧
      HasParity ((B*E-(1-X^2)*C*F).map Complex.ofRealHom) (k+l) ∧
      HasParity ((B*F+C*E).map Complex.ofRealHom) (k+l+1) := by
  refine ⟨by rw [hA,hD];ring,?_,?_,?_,?_⟩
  · apply (degree_sub_le _ _).trans
    apply max_le
    · simpa using degree_mul_le_of_le hB hE
    · exact degree_gap_mul hC hF
  · apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact degree_mul_lt_right hB hF
    · rw [mul_comm C E,Nat.add_comm k l]
      exact degree_mul_lt_right hE hC
  · simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_one,Polynomial.map_pow,Polynomial.map_X]
    apply parity_sub (parity_mul hpB hpE)
    have h := parity_mul (parity_mul parity_gap hpC) hpF
    have he : 0+(k+1)+(l+1) = k+l+2 := by omega
    rw [he] at h
    exact (parity_shift _ _).mp h
  · simp only [Polynomial.map_add,Polynomial.map_mul]
    apply parity_add
    · simpa only [show k+(l+1)=k+l+1 by omega] using parity_mul hpB hpF
    · simpa only [show (k+1)+l=k+l+1 by omega] using parity_mul hpC hpE
end QSVTCert

noncomputable section
open Polynomial
set_option autoImplicit false
namespace QSVTEven
lemma neg_coeff (P : ℝ[X]) (i : ℕ) :
    (P.comp (-X)).coeff i = (-1:ℝ)^i * P.coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    simp only [monomial_comp, show (-X : ℝ[X]) = (-1:ℝ) • X by simp,
      _root_.smul_pow, coeff_C_mul, coeff_smul, smul_eq_mul, coeff_X_pow, coeff_monomial]
    by_cases e : n=i
    · subst i; simp [mul_comm]
    · simp only [if_neg e, if_neg (Ne.symm e), mul_zero]

lemma even_contract (A : ℝ[X]) (he : A.comp (-X) = A) :
    (contract 2 A).comp (X^2) = A := by
  have hodd (n : ℕ) (hn : ¬ 2 ∣ n) : A.coeff n = 0 := by
    have h := congrArg (fun p : ℝ[X] => p.coeff n) he
    simp only [neg_coeff] at h
    have hmod : n % 2 = 1 := by omega
    rw [neg_one_pow_eq_pow_mod_two,hmod] at h
    norm_num at h
    linarith
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand (by decide : 0 < 2)]
  split_ifs with hn
  · rw [coeff_contract (by decide : (2:ℕ) ≠ 0)]
    congr 1
    exact Nat.div_mul_cancel hn
  · exact (hodd n hn).symm
lemma contract_degree (A : ℝ[X]) (k : ℕ) (he : A.comp (-X) = A)
    (hd : A.degree ≤ (2*k : ℕ)) : (contract 2 A).natDegree ≤ k := by
  have h := congrArg Polynomial.natDegree (even_contract A he)
  rw [← expand_eq_comp_X_pow,natDegree_expand] at h
  have hA : A.natDegree ≤ 2*k := natDegree_le_iff_degree_le.mpr hd
  omega
lemma contract_nonneg (A : ℝ[X]) (he : A.comp (-X) = A)
    (hp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (contract 2 A).eval y := by
  intro y hy
  have hs : Real.sqrt y ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨(by linarith [Real.sqrt_nonneg y]),(Real.sqrt_le_one).mpr hy.2⟩
  have h := hp (Real.sqrt y) hs
  rw [← even_contract A he,eval_comp,eval_pow,eval_X,Real.sq_sqrt hy.1] at h
  exact h
end QSVTEven

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


open Polynomial
namespace QSVTGlobal
set_option autoImplicit false

lemma quotient_nonneg (p q : ℝ[X]) (a : ℝ)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) (he : p = (X - C a) ^ 2 * q) :
    ∀ x : ℝ, 0 ≤ q.eval x := by
  have h : ∀ x ∈ ({a}ᶜ : Set ℝ), 0 ≤ q.eval x := by
    intro x hx
    have hx' : x - a ≠ 0 := sub_ne_zero.mpr (by simpa using hx)
    have hpos : 0 < (x-a)^2 := sq_pos_of_ne_zero hx'
    have := hp x
    rw [he, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
    exact nonneg_of_mul_nonneg_right this hpos
  exact fun x => (closure_minimal h (isClosed_le continuous_const q.continuous))
    (dense_compl_singleton a x)

lemma square_factor (p : ℝ[X]) (a : ℝ)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) (ha : p.eval a = 0) :
    ∃ q : ℝ[X], p = (X - C a)^2 * q := by
  have hmin : IsLocalMin (fun x : ℝ => p.eval x) a := by
    apply IsMinOn.isLocalMin (s := Set.univ)
    · intro x _; simpa [ha] using hp x
    · exact Filter.univ_mem
  have hd : p.derivative.eval a = 0 := hmin.hasDerivAt_eq_zero (p.hasDerivAt a)
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr ha : X - C a ∣ p)
  have hqa : q.eval a = 0 := by
    rw [hq, derivative_mul] at hd
    simpa using hd
  obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hqa : X - C a ∣ q)
  exact ⟨r, by rw [hq, hr]; ring⟩

lemma nonneg_two_squares (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ a b : ℝ[X], p = a^2 + b^2 := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hz : p = 0
    · exact ⟨0, 0, by simp [hz]⟩
    by_cases hc : p.natDegree = 0
    · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hc
      have h0 : 0 ≤ p.coeff 0 := by
        have hh := hp 0
        rw [he] at hh
        simpa only [eval_C] using hh
      exact ⟨C (Real.sqrt (p.coeff 0)), 0, by
        calc
          p = C (p.coeff 0) := he
          _ = C (Real.sqrt (p.coeff 0)) ^ 2 + 0 ^ 2 := by
            simp only [← C_pow, Real.sq_sqrt h0, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow, add_zero]⟩
    by_cases hr : ∃ a : ℝ, p.eval a = 0
    · obtain ⟨a, ha⟩ := hr
      obtain ⟨q, hq⟩ := square_factor p a hp ha
      have hq0 : q ≠ 0 := by intro h; simp [h] at hq; exact hz hq
      have hdeg : q.natDegree < n := by
        have hd := congrArg Polynomial.natDegree hq
        rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hq0,
          natDegree_pow, natDegree_X_sub_C] at hd
        omega
      obtain ⟨u, v, huv⟩ := ih q.natDegree hdeg q (quotient_nonneg p q a hp hq) rfl
      exact ⟨(X-C a)*u, (X-C a)*v, by rw [hq, huv]; ring⟩
    · obtain ⟨z, hz'⟩ : ∃ z : ℂ, aeval z p = 0 :=
        IsAlgClosed.exists_aeval_eq_zero ℂ p (by
          rw [degree_eq_natDegree hz]; exact_mod_cast (Nat.pos_of_ne_zero hc).ne')
      have him : z.im ≠ 0 := by
        intro he
        have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [he]
        apply hr
        refine ⟨z.re, ?_⟩
        have := hz'
        rw [hzreal] at this
        change (aeval (algebraMap ℝ ℂ z.re) p) = 0 at this
        rw [aeval_algebraMap_apply_eq_algebraMap_eval] at this
        apply Complex.ofReal_injective
        exact this
      let Q : ℝ[X] := X^2 - C (2*z.re)*X + C (‖z‖^2)
      have hQ : Q = (X-C z.re)^2 + (C z.im)^2 := by
        dsimp [Q]
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [map_add, map_mul, map_ofNat]
        ring
      have hQpos : ∀ x : ℝ, 0 < Q.eval x := by
        intro x
        rw [hQ]
        simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
        nlinarith [sq_nonneg (x-z.re), sq_pos_of_ne_zero him]
      obtain ⟨q, hq⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz' him
      change p = Q * q at hq
      have hq0 : q ≠ 0 := by intro h; simp [h] at hq; exact hz hq
      have hQ0 : Q ≠ 0 := by intro h; have := hQpos 0; simp [h] at this
      have hQdeg : Q.natDegree = 2 := by
        dsimp [Q]
        compute_degree!
      have hdeg : q.natDegree < n := by
        have hd := congrArg Polynomial.natDegree hq
        rw [natDegree_mul hQ0 hq0, hQdeg] at hd
        omega
      have hqp : ∀ x : ℝ, 0 ≤ q.eval x := by
        intro x
        have := hp x
        rw [hq, eval_mul] at this
        exact nonneg_of_mul_nonneg_right this (hQpos x)
      obtain ⟨u, v, huv⟩ := ih q.natDegree hdeg q hqp rfl
      refine ⟨(X-C z.re)*u-C z.im*v, (X-C z.re)*v+C z.im*u, ?_⟩
      rw [hq, hQ, huv]
      ring


open scoped ComplexConjugate
lemma cj_real (p : ℝ[X]) : (p.map Complex.ofRealHom).map (starRingEnd ℂ) = p.map Complex.ofRealHom := by
  ext n
  simp [coeff_map]
lemma spectral_factor (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ W : ℂ[X], p.map Complex.ofRealHom = W * W.map (starRingEnd ℂ) := by
  obtain ⟨a,b,hab⟩ := nonneg_two_squares p hp
  let W : ℂ[X] := a.map Complex.ofRealHom + Polynomial.C Complex.I * b.map Complex.ofRealHom
  have hc : W.map (starRingEnd ℂ) = a.map Complex.ofRealHom - Polynomial.C Complex.I * b.map Complex.ofRealHom := by
    simp only [W,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,cj_real]
    simp [sub_eq_add_neg]
  refine ⟨W,?_⟩
  rw [hc,hab,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_pow]
  dsimp [W]
  have hi : (Polynomial.C Complex.I : ℂ[X])^2 = -1 := by rw [← C_pow,Complex.I_sq];simp
  calc
    _ = (a.map Complex.ofRealHom)^2 - (Polynomial.C Complex.I)^2*(b.map Complex.ofRealHom)^2 := by rw [hi];ring
    _ = _ := by ring
end QSVTGlobal

noncomputable section
open Polynomial
set_option autoImplicit false
namespace QSVTSigns
lemma divide_at (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) :
    ∃ q : ℝ[X], p = (C r-X)*q := by
  obtain ⟨q,hq⟩ := (dvd_iff_isRoot.mpr hr : X-C r ∣ p)
  exact ⟨-q,by rw [hq];ring⟩
lemma opposite (p : ℝ[X]) (r : ℝ)
    (hl : ∀ x : ℝ, x ≤ r → 0 ≤ p.eval x)
    (hr : ∀ x : ℝ, r ≤ x → p.eval x ≤ 0) :
    ∃ q : ℝ[X], p = (C r-X)*q ∧ ∀ x : ℝ, 0 ≤ q.eval x := by
  obtain ⟨q,hq⟩ := divide_at p r (le_antisymm (hr r le_rfl) (hl r le_rfl))
  refine ⟨q,hq,?_⟩
  have h : ∀ x ∈ ({r}ᶜ : Set ℝ), 0 ≤ q.eval x := by
    intro x hx
    have hn : x ≠ r := by simpa using hx
    rcases lt_or_gt_of_ne hn with hx|hx
    · have hp := hl x hx.le
      rw [hq,eval_mul,eval_sub,eval_C,eval_X] at hp
      exact nonneg_of_mul_nonneg_right hp (by linarith)
    · have hp := hr x hx.le
      rw [hq,eval_mul,eval_sub,eval_C,eval_X] at hp
      have hneg : 0 ≤ (x-r)*q.eval x := by nlinarith only [hp]
      exact nonneg_of_mul_nonneg_right hneg (by linarith)
  exact fun x => (closure_minimal h (isClosed_le continuous_const q.continuous))
    (dense_compl_singleton r x)
lemma divide_one (p : ℝ[X])
    (hi : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ p.eval x)
    (ho : ∀ x : ℝ, 1 ≤ x → p.eval x ≤ 0) :
    ∃ q : ℝ[X], p = (1-X)*q ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ q.eval x) := by
  obtain ⟨q,hq⟩ := divide_at p 1 (le_antisymm (ho 1 le_rfl) (hi 1 (by norm_num)))
  have he : p = (1-X)*q := by simpa using hq
  refine ⟨q,he,?_⟩
  have hin : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ q.eval x := by
    intro x hx
    have hh := hi x ⟨hx.1.le,hx.2.le⟩
    rw [he,eval_mul,eval_sub,eval_one,eval_X] at hh
    exact nonneg_of_mul_nonneg_right hh (by linarith [hx.2])
  have hc : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ q.eval x := by
    have hh := closure_minimal hin (isClosed_le continuous_const q.continuous)
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hh
    exact hh
  intro x hx
  by_cases h1 : x ≤ 1
  · exact hc x ⟨hx,h1⟩
  · have hp := ho x (by linarith)
    rw [he,eval_mul,eval_sub,eval_one,eval_X] at hp
    have hh : 0 ≤ (x-1)*q.eval x := by nlinarith only [hp]
    exact nonneg_of_mul_nonneg_right hh (by linarith)
end QSVTSigns

noncomputable section
open Polynomial QAlgorithms
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTCompletion
open QSVTReq
lemma cj_invol (p : ℂ[X]) : cj (cj p) = p := by
  ext n
  simp [cj,coeff_map]
lemma cj_parity {p : ℂ[X]} {k : ℕ} (h : HasParity p k) : HasParity (cj p) k := by
  unfold HasParity at *
  rw [smul_eq_C_mul] at h ⊢
  have hh := congrArg (Polynomial.map (starRingEnd ℂ)) h
  simpa [Polynomial.map_comp,Polynomial.map_mul,Polynomial.map_C,cj] using hh
lemma real_lift (p : ℂ[X]) (h : cj p = p) : ∃ a : ℝ[X], a.map Complex.ofRealHom = p := by
  apply (mem_lifts p).mp
  apply (lifts_iff_coeff_lifts p).mpr
  intro n
  have hh := congrArg (fun q : ℂ[X] => (q.coeff n).im) h
  simp only [cj,coeff_map,Complex.conj_im] at hh
  have hi : (p.coeff n).im = 0 := by linarith
  refine ⟨(p.coeff n).re,?_⟩
  apply Complex.ext <;> simp [hi]
lemma residual (k : ℕ) (P : ℂ[X]) (hp : HasParity P k) :
    ∃ A : ℝ[X], A.map Complex.ofRealHom = 1-P*cj P ∧ A.comp (-X)=A := by
  have hfix : cj (1-P*cj P) = 1-P*cj P := by
    simp only [cj,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_mul]
    change 1-cj P*cj (cj P) = 1-P*cj P
    rw [cj_invol,mul_comm]
  obtain ⟨A,hA⟩ := real_lift _ hfix
  refine ⟨A,hA,?_⟩
  have he := QSVTCert.parity_mul hp (cj_parity hp)
  have hs : (-1:ℂ)^(k+k) = 1 := by rw [← two_mul,pow_mul];simp
  change (P*cj P).comp (-X) = (-1:ℂ)^(k+k) • (P*cj P) at he
  rw [hs,one_smul] at he
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa only [Polynomial.map_comp,Polynomial.map_neg,Polynomial.map_X,hA,sub_comp,one_comp,he]
lemma eval_real (p : ℝ[X]) (x : ℝ) :
    (p.map Complex.ofRealHom).eval (x:ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [eval_map]
  exact Polynomial.eval₂_at_apply (p := p) Complex.ofRealHom x
lemma residual_eval (P : ℂ[X]) (A : ℝ[X]) (hA : A.map Complex.ofRealHom = 1-P*cj P) (x : ℝ) :
    A.eval x = 1-‖P.eval (x:ℂ)‖^2 := by
  have h := congrArg (Polynomial.eval (x:ℂ)) hA
  rw [eval_real,eval_sub,eval_one,norm_eval] at h
  exact_mod_cast h
lemma residual_complex (P : ℂ[X]) (A : ℝ[X]) (hA : A.map Complex.ofRealHom = 1-P*cj P)
    (he : A.comp (-X)=A) (z : ℂ) :
    ((contract 2 A).map Complex.ofRealHom).eval (z^2) = 1-P.eval z*(cj P).eval z := by
  have h := congrArg (Polynomial.map Complex.ofRealHom) (QSVTEven.even_contract A he)
  rw [Polynomial.map_comp,Polynomial.map_pow,Polynomial.map_X,hA] at h
  have hh := congrArg (Polynomial.eval z) h
  simpa only [eval_comp,eval_pow,eval_X,eval_sub,eval_one,eval_mul] using hh
lemma residual_signs (k : ℕ) (P : ℂ[X]) (A : ℝ[X])
    (hp : HasParity P k) (hA : A.map Complex.ofRealHom = 1-P*cj P) (he : A.comp (-X)=A)
    (hi : ∀ x ∈ Set.Icc (-1:ℝ) 1, ‖P.eval (x:ℂ)‖ ≤ 1)
    (ho : ∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x:ℂ)‖)
    (hc : Even k → ∀ x : ℝ, (1:ℂ) ≤ P.eval (Complex.I*x)*(cj P).eval (Complex.I*x)) :
    (∀ y ∈ Set.Icc (0:ℝ) 1, 0 ≤ (contract 2 A).eval y) ∧
    (∀ y : ℝ, 1 ≤ y → (contract 2 A).eval y ≤ 0) ∧
    (∀ y : ℝ, y ≤ 0 →
      (Even k → (contract 2 A).eval y ≤ 0) ∧
      (Odd k → 0 ≤ (contract 2 A).eval y)) := by
  refine ⟨?_,?_,?_⟩
  · apply QSVTEven.contract_nonneg A he
    intro x hx
    rw [residual_eval P A hA]
    have hh := hi x hx
    nlinarith [norm_nonneg (P.eval (x:ℂ))]
  · intro y hy
    have hs : 1 ≤ Real.sqrt y := (Real.one_le_sqrt).mpr hy
    have hh := ho (Real.sqrt y) (by simpa [abs_of_nonneg (Real.sqrt_nonneg y)] using hs)
    have hv := residual_eval P A hA (Real.sqrt y)
    rw [← QSVTEven.even_contract A he,eval_comp,eval_pow,eval_X,
      Real.sq_sqrt (by linarith : 0 ≤ y)] at hv
    nlinarith [norm_nonneg (P.eval (Real.sqrt y:ℂ))]
  · intro y hy
    let x : ℝ := Real.sqrt (-y)
    have hs : x^2 = -y := Real.sq_sqrt (by linarith)
    have hz : (Complex.I*(x:ℂ))^2 = (y:ℂ) := by
      rw [mul_pow,Complex.I_sq]
      have hs' : (x:ℂ)^2 = -(y:ℂ) := by exact_mod_cast hs
      rw [hs'];ring
    have hh := residual_complex P A hA he (Complex.I*x)
    rw [hz,eval_real] at hh
    constructor
    · intro hk
      have hr := (hc hk x).1
      have hh' := congrArg Complex.re hh
      simp only [Complex.ofReal_re,Complex.sub_re,Complex.one_re] at hh'
      change 1 ≤ (P.eval (Complex.I*x)*(cj P).eval (Complex.I*x)).re at hr
      linarith
    · intro hk
      have hs : (-1:ℂ)^k = -1 := hk.neg_one_pow
      have hz' : conj (Complex.I*(x:ℂ)) = -(Complex.I*x) := by simp
      have hconj : (cj P).eval (Complex.I*x) = -conj (P.eval (Complex.I*x)) := by
        rw [cj_eval_any,hz',parity_eval hp,hs,neg_one_mul,map_neg]
      rw [hconj,mul_neg,Complex.mul_conj,Complex.normSq_eq_norm_sq] at hh
      have hh' := congrArg Complex.re hh
      simp only [Complex.ofReal_re,Complex.sub_re,Complex.one_re,Complex.neg_re] at hh'
      nlinarith [sq_nonneg ‖P.eval (Complex.I*x)‖]
end QSVTCompletion

noncomputable section
open Polynomial QAlgorithms
open scoped ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTCompletion
open QSVTReq
lemma cj_comp_square (p : ℂ[X]) : cj (p.comp (X^2)) = (cj p).comp (X^2) := by
  simp only [cj,Polynomial.map_comp,Polynomial.map_pow,Polynomial.map_X]
lemma comp_square_even (p : ℂ[X]) : (p.comp (X^2)).comp (-X) = p.comp (X^2) := by
  rw [comp_assoc]
  simp
lemma factor_completion (k : ℕ) (P : ℂ[X]) (hp : HasParity P k)
    (hi : ∀ x ∈ Set.Icc (-1:ℝ) 1, ‖P.eval (x:ℂ)‖ ≤ 1)
    (ho : ∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x:ℂ)‖)
    (hc : Even k → ∀ x : ℝ, (1:ℂ) ≤ P.eval (Complex.I*x)*(cj P).eval (Complex.I*x)) :
    ∃ Q : ℂ[X], normal P Q ∧ HasParity Q (k+1) := by
  obtain ⟨A,hA,he⟩ := residual k P hp
  let F := contract 2 A
  obtain ⟨hFi,hFo,hFn⟩ := residual_signs k P A hp hA he hi ho hc
  obtain ⟨g,hg,hgpos⟩ := QSVTSigns.divide_one F hFi hFo
  have hF : (F.map Complex.ofRealHom).comp (X^2) = 1-P*cj P := by
    have hh := congrArg (Polynomial.map Complex.ofRealHom) (QSVTEven.even_contract A he)
    simpa only [Polynomial.map_comp,Polynomial.map_pow,Polynomial.map_X,hA] using hh
  rcases Nat.even_or_odd k with hk|hk
  · have hgneg : ∀ x : ℝ, x ≤ 0 → g.eval x ≤ 0 := by
      intro x hx
      have hh := (hFn x hx).1 hk
      change F.eval x ≤ 0 at hh
      rw [hg,eval_mul,eval_sub,eval_one,eval_X] at hh
      have hpos : 0 < 1-x := by linarith
      by_contra hn
      have : 0 < (1-x)*g.eval x := mul_pos hpos (by linarith)
      linarith
    obtain ⟨h,hh,hpos⟩ := QSVTSigns.opposite (-g) 0
      (by intro x hx; simpa using neg_nonneg.mpr (hgneg x hx))
      (by intro x hx; simpa using neg_nonpos.mpr (hgpos x hx))
    have hgh : g = X*h := by
      have hh' : -g = -X*h := by simpa using hh
      linear_combination -hh'
    obtain ⟨W,hW⟩ := QSVTGlobal.spectral_factor h hpos
    let Q : ℂ[X] := X*W.comp (X^2)
    refine ⟨Q,?_,?_⟩
    · have hres : 1-P*cj P = (1-X^2)*(Q*cj Q) := by
        rw [← hF,hg,hgh]
        simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,
          Polynomial.map_X,hW,mul_comp,sub_comp,one_comp,X_comp,cj_comp_square,
          cj,Polynomial.map_mul,Polynomial.map_X]
        dsimp [Q]
        simp only [cj,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_comp,
          Polynomial.map_pow,Polynomial.map_X]
        ring
      unfold normal
      linear_combination -hres
    · have hs : (-1:ℂ)^(k+1) = -1 := by rw [pow_succ,hk.neg_one_pow];ring
      simp only [Q,HasParity,mul_comp,X_comp,comp_square_even,hs,neg_one_smul]
      ring
  · have hgall : ∀ x : ℝ, 0 ≤ g.eval x := by
      intro x
      by_cases hx : 0 ≤ x
      · exact hgpos x hx
      · have hh := (hFn x (by linarith)).2 hk
        change 0 ≤ F.eval x at hh
        rw [hg,eval_mul,eval_sub,eval_one,eval_X] at hh
        exact nonneg_of_mul_nonneg_right hh (by linarith)
    obtain ⟨W,hW⟩ := QSVTGlobal.spectral_factor g hgall
    let Q : ℂ[X] := W.comp (X^2)
    refine ⟨Q,?_,?_⟩
    · have hres : 1-P*cj P = (1-X^2)*(Q*cj Q) := by
        rw [← hF,hg]
        simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,
          Polynomial.map_X,hW,mul_comp,sub_comp,one_comp,X_comp]
        dsimp [Q]
        rw [cj_comp_square]
      unfold normal
      linear_combination -hres
    · have hs : (-1:ℂ)^(k+1) = 1 := by rw [pow_succ,hk.neg_one_pow];ring
      simp only [Q,HasParity,comp_square_even,hs,one_smul]
lemma degree_completion (k : ℕ) (P Q : ℂ[X]) (hp : P.degree ≤ k) (hn : normal P Q) :
    Q.degree < k := by
  have hcj : ∀ p : ℂ[X], (cj p).degree = p.degree := by
    intro p
    exact le_antisymm (degree_map_le) (by simpa only [cj_invol] using (degree_map_le : (cj (cj p)).degree ≤ (cj p).degree))
  have hP : (P*cj P).degree ≤ (2*k : ℕ) := by
    have hcp : (cj P).degree ≤ k := by rwa [hcj]
    have hh := degree_mul_le_of_le hp hcp
    simpa [two_mul] using hh
  have hR : (1-P*cj P).degree ≤ (2*k : ℕ) := by
    apply (degree_sub_le _ _).trans
    exact max_le (by simp) hP
  have he : (1-X^2)*(Q*cj Q) = 1-P*cj P := by
    unfold normal at hn
    linear_combination hn
  by_cases hq : Q = 0
  · rw [hq,degree_zero]; exact WithBot.bot_lt_coe k
  have hd : (1-X^2 : ℂ[X]).degree = 2 := by compute_degree!
  have hh := congrArg Polynomial.degree he
  rw [degree_mul,degree_mul,hd,hcj,degree_eq_natDegree hq] at hh
  have hh' : 2+Q.natDegree+Q.natDegree ≤ 2*k := by
    have hh'' : (2:WithBot ℕ)+↑Q.natDegree+↑Q.natDegree ≤ ↑(2*k) := by
      rw [← add_assoc] at hh
      rw [hh]
      exact hR
    exact_mod_cast hh''
  rw [degree_eq_natDegree hq]
  exact_mod_cast (show Q.natDegree < k by omega)
theorem complete (k : ℕ) (P : ℂ[X]) :
    (∃ Q : ℂ[X], QSVT19.Main.IsQSPPair k P Q) ↔
    ((P.degree ≤ k ∧ HasParity P k) ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, ‖P.eval (x:ℂ)‖ ≤ 1) ∧
    (∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x:ℂ)‖) ∧
    (Even k → ∀ x : ℝ, (1:ℂ) ≤ P.eval (Complex.I*x)*(cj P).eval (Complex.I*x))) := by
  constructor
  · rintro ⟨Q,h⟩
    exact ⟨⟨h.1.1,h.2.1.1⟩,QSVTReq.pair_conditions k P Q h⟩
  · rintro ⟨⟨hd,hp⟩,hi,ho,hc⟩
    obtain ⟨Q,hn,hq⟩ := factor_completion k P hp hi ho hc
    exact ⟨Q,⟨hd,degree_completion k P Q hd hn⟩,⟨hp,hq⟩,(normal_iff P Q).mp hn⟩
end QSVTCompletion

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 4 (first claim), p. 10: "Let k ∈ N be fixed. Let P ∈ C[x], there exists some
Q ∈ C[x] such that P, Q satisfy properties (i)-(iii) of Theorem 3 if and only if P satisfies
properties (i)-(ii) of Theorem 3 and
(iv.a) ∀x ∈ [−1, 1]: |P(x)| ≤ 1
(iv.b) ∀x ∈ (−∞, −1] ∪ [1, ∞): |P(x)| ≥ 1
(iv.c) if k is even, then ∀x ∈ R: P(ix)P^∗(ix) ≥ 1."

**Formalization Note.** Properties (i)–(iii) of Theorem 3 are `IsQSPPair k P Q`; (i)–(ii) for
`P` alone are `deg P ≤ k` and parity `k mod 2`. `P^*` is `P.map (starRingEnd ℂ)`. In (iv.c) the
comparison `1 ≤ z` of complex numbers is Mathlib's `ComplexOrder`: `z` is real and at least
`1`. The second claim of Theorem 4 ((v.a)–(v.b), about `Q`) is not part of this statement. -/
theorem solution (k : ℕ) (P : ℂ[X]) :
    (∃ Q : ℂ[X], IsQSPPair k P Q) ↔ ((P.degree ≤ k ∧ QAlgorithms.HasParity P k) ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) ∧ (∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x : ℂ)‖) ∧ (Even k → ∀ x : ℝ, (1 : ℂ) ≤ P.eval (Complex.I * x) * (P.map (starRingEnd ℂ)).eval (Complex.I * x))) := by
  exact QSVTCompletion.complete k P