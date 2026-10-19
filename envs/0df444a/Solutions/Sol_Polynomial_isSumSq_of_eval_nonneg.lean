-- Prove2me | solution 1 for Polynomial.isSumSq_of_eval_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:13:33.833074+00:00
-- url     : https://prove2.me/submissions/3c78a845-33ca-49c1-adc1-8b39b5da9a59

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Polynomial
set_option autoImplicit false

private lemma quotient_nonneg (p q : ℝ[X]) (a : ℝ)
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

private lemma square_factor (p : ℝ[X]) (a : ℝ)
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

private lemma nonneg_two_squares (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
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

theorem solution (p : Polynomial ℝ) (hp : ∀ x : ℝ, 0 ≤ p.eval x) : IsSumSq p := by
  obtain ⟨a,b,hab⟩ := nonneg_two_squares p hp
  rw [hab, pow_two, pow_two]
  exact (IsSumSq.mul_self a).add (IsSumSq.mul_self b)
