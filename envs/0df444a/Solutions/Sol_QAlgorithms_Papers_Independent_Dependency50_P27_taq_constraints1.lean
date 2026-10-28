-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.taq_constraints1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:26:11.204573+00:00
-- url     : https://prove2.me/submissions/3b40bae7-bd59-4e79-a6fb-d3d6782b9d6f

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial

lemma S170bF_sgr_neg {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {y : R} (h : y < 0) :
    sgr y = -1 := by simp [sgr, h.ne, not_lt.2 h.le]

lemma S170bF_sgr_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {y : R} (h : 0 < y) :
    sgr y = 1 := by simp [sgr, h.ne', h]

lemma S170bF_main {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (z : List R) (q : Polynomial R) :
    taq z q = (constraints1 z q 1 : ℤ) - (constraints1 z q (-1) : ℤ) ∧
    taq z (q ^ 2) = (constraints1 z q 1 : ℤ) + (constraints1 z q (-1) : ℤ) ∧
    taq z 1 = (constraints1 z q 1 : ℤ) + (constraints1 z q (-1) : ℤ) +
      (constraints1 z q 0 : ℤ) := by
  induction z with
  | nil => simp [taq, constraints1]
  | cons x z ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [taq, constraints1, List.map_cons, List.sum_cons, List.filter_cons, Polynomial.eval_pow,
      Polynomial.eval_one] at *
    have s1 : sgr (1 : R) = 1 := S170bF_sgr_pos one_pos
    rcases lt_trichotomy (q.eval x) 0 with h | h | h
    · have hs := S170bF_sgr_neg h
      have hs2 : sgr (q.eval x ^ 2) = 1 := S170bF_sgr_pos (by nlinarith)
      simp only [hs, hs2, s1]
      norm_num [s1] at h3 ⊢
      omega
    · have hs : sgr (q.eval x) = 0 := by simp [sgr, h]
      have hs2 : sgr (q.eval x ^ 2) = 0 := by simp [sgr, h]
      simp only [hs, hs2, s1]
      norm_num [s1] at h3 ⊢
      omega
    · have hs := S170bF_sgr_pos h
      have hs2 : sgr (q.eval x ^ 2) = 1 := S170bF_sgr_pos (by positivity)
      simp only [hs, hs2, s1]
      norm_num [s1] at h3 ⊢
      omega


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (z : List R) (q : Polynomial R) :
    taq z q = (constraints1 z q 1 : ℤ) - (constraints1 z q (-1) : ℤ) ∧
    taq z (q ^ 2) = (constraints1 z q 1 : ℤ) + (constraints1 z q (-1) : ℤ) ∧
    taq z 1 = (constraints1 z q 1 : ℤ) + (constraints1 z q (-1) : ℤ) +
      (constraints1 z q 0 : ℤ) := by
  exact S170bF_main z q

end
