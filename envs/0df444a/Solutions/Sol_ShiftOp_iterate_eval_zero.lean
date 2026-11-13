-- Prove2me | solution 1 for ShiftOp.iterate_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:04:29.212197+00:00
-- url     : https://prove2.me/submissions/e421b92e-9263-43a7-8ec6-30731c45bf53

import Mathlib

open MvPolynomial Finset

namespace ShiftOpAux

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- the linear form `w · x` -/
noncomputable def lin (w : σ → R) : MvPolynomial σ R := ∑ i, C (w i) * X i

/-- iterated partial derivative along a word -/
noncomputable def wordD (l : List σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  l.foldr (fun j q => pderiv j q) p

/-- the constant-coefficient operator `Σ_t c(t) ∂_{t 0} ⋯ ∂_{t (r-1)}` -/
noncomputable def op (r : ℕ) (c : (Fin r → σ) → R) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ t, c t • wordD (List.ofFn t) p

/-- its symbol `g(w) = Σ_t c(t) ∏_s w (t s)` -/
def symb (r : ℕ) (c : (Fin r → σ) → R) (w : σ → R) : R := ∑ t, c t * ∏ s, w (t s)

lemma pderiv_lin (w : σ → R) (j : σ) : pderiv j (lin w) = C (w j) := by
  classical
  unfold lin
  rw [map_sum]
  simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']; simp

omit [Fintype σ] in
lemma wordD_C_mul (l : List σ) (a : R) (p : MvPolynomial σ R) :
    wordD l (C a * p) = C a * wordD l p := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [wordD, List.foldr_cons] at ih ⊢
    rw [ih, pderiv_C_mul]

lemma wordD_lin_pow (w : σ → R) (l : List σ) (E : ℕ) :
    wordD l (lin w ^ E) =
      C ((E.descFactorial l.length : R) * (l.map w).prod) * lin w ^ (E - l.length) := by
  induction l with
  | nil => simp [wordD]
  | cons j l ih =>
    have h : wordD (j :: l) (lin w ^ E) = pderiv j (wordD l (lin w ^ E)) := rfl
    rw [h, ih, pderiv_C_mul, Derivation.leibniz_pow, pderiv_lin, List.length_cons,
      Nat.descFactorial_succ, List.map_cons, List.prod_cons, Nat.sub_sub]
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, map_mul, map_natCast]
    ring

lemma op_C_mul (r : ℕ) (c : (Fin r → σ) → R) (a : R) (p : MvPolynomial σ R) :
    op r c (C a * p) = C a * op r c p := by
  unfold op
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [wordD_C_mul, smul_eq_C_mul, smul_eq_C_mul]; ring

lemma op_lin_pow (r : ℕ) (c : (Fin r → σ) → R) (w : σ → R) (E : ℕ) :
    op r c (lin w ^ E) = C ((E.descFactorial r : R) * symb r c w) * lin w ^ (E - r) := by
  unfold op symb
  simp only [wordD_lin_pow, List.length_ofFn, List.map_ofFn, List.prod_ofFn, smul_eq_C_mul,
    ← mul_assoc, ← map_mul, ← sum_mul, ← map_sum, mul_sum]
  congr 2
  refine sum_congr rfl fun t _ => ?_
  simp only [Function.comp_def]; ring

lemma iterate_op_lin_pow (r : ℕ) (c : (Fin r → σ) → R) (w : σ → R) (E m : ℕ) :
    (op r c)^[m] (lin w ^ E) =
      C ((E.descFactorial (m * r) : R) * symb r c w ^ m) * lin w ^ (E - m * r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, op_C_mul, op_lin_pow, ← mul_assoc, ← map_mul,
      Nat.sub_sub, ← Nat.succ_mul]
    congr 2
    have := Nat.descFactorial_mul_descFactorial (n := E) (Nat.le_add_right (m * r) r)
    rw [Nat.add_sub_cancel_left, ← Nat.succ_mul] at this
    rw [← this, Nat.cast_mul, pow_succ]; ring

lemma eval_zero_lin (w : σ → R) : eval 0 (lin w) = 0 := by
  simp [lin]

end ShiftOpAux

open ShiftOpAux in
theorem solution {σ R : Type*} [Fintype σ] [CommSemiring R]
    (r : ℕ) (c : (Fin r → σ) → R) (w : σ → R) (m E : ℕ) :
    MvPolynomial.eval 0
      ((fun p : MvPolynomial σ R =>
          ∑ t : Fin r → σ, c t • (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv j q) p)^[m]
        ((∑ i, MvPolynomial.C (w i) * MvPolynomial.X i) ^ E)) =
      if E = m * r then
        ((m * r).factorial : R) * (∑ t : Fin r → σ, c t * ∏ s, w (t s)) ^ m
      else 0 := by
  have h := iterate_op_lin_pow r c w E m
  unfold op wordD lin symb at h
  rw [h, eval_mul, eval_C, eval_pow, ← lin, eval_zero_lin]
  split_ifs with hE
  · subst hE; simp [Nat.descFactorial_self]
  · rcases lt_or_gt_of_ne hE with hlt | hgt
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hlt]; simp
    · rw [zero_pow (by omega), mul_zero]
