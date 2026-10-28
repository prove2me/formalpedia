-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.lcoef_cpsP
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:28:35.072832+00:00
-- url     : https://prove2.me/submissions/683026e3-3b46-43a1-a154-aa04bba70cff

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial

lemma S170bI_zero {R : Type*} [Field R] [LinearOrder R] (e : List R) :
    ∀ q : PolyF R, qfEval e (polyZeroF q) = true ↔ evalPoly e q = 0 := by
  intro q
  induction q with
  | nil => simp [polyZeroF, qfEval, evalPoly]
  | cons a q ih =>
    simp only [polyZeroF, qfEval, evalPoly, Bool.and_eq_true, decide_eq_true_eq, ih]
    simp only [evalTerm]
    constructor
    · rintro ⟨ha, hq⟩; rw [ha, hq]; simp
    · intro h
      have h0 := congrArg (fun r => Polynomial.coeff r 0) h
      simp at h0
      refine ⟨h0, ?_⟩
      rw [h0, map_zero, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left Polynomial.X_ne_zero

lemma S170bI_lc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (k : Term R → Formula R) (kbar : R → Bool)
    (hk : ∀ (x : Term R) (e : List R), qfEval e (k x) = kbar (evalTerm e x)) :
    ∀ (p : PolyF R) (e : List R),
      qfEval e (lcoefCps p k) = kbar (evalPoly e p).leadingCoeff := by
  intro p e
  induction p with
  | nil => simp [lcoefCps, evalPoly, hk, evalTerm]
  | cons a q ih =>
    simp only [lcoefCps, ifCps, qfEval, ih, hk, evalPoly]
    by_cases hq : evalPoly e q = 0
    · have := (S170bI_zero e q).2 hq
      rw [this, hq]; simp
    · have : qfEval e (polyZeroF q) = false := by
        rw [← Bool.not_eq_true, S170bI_zero]; exact hq
      rw [this]
      simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
      congr 1
      rw [mul_comm Polynomial.X, Polynomial.leadingCoeff_add_of_degree_lt, Polynomial.leadingCoeff_mul_X]
      rw [Polynomial.degree_mul_X]
      refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      have : (0 : WithBot ℕ) ≤ (evalPoly e q).degree := Polynomial.zero_le_degree_iff.2 hq
      exact lt_of_le_of_lt this (by
        rcases h : (evalPoly e q).degree with _ | d
        · exact absurd (Polynomial.degree_eq_bot.1 h) hq
        · exact WithBot.coe_lt_coe.2 (Nat.lt_succ_self d))

theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (k : Term R → Formula R) (kbar : R → Bool)
    (hk : ∀ (x : Term R) (e : List R), qfEval e (k x) = kbar (evalTerm e x)) :
    ∀ (p : PolyF R) (e : List R),
      qfEval e (lcoefCps p k) = kbar (evalPoly e p).leadingCoeff := by
  exact S170bI_lc k kbar hk

end
