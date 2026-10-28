-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.positive_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:26:31.432806+00:00
-- url     : https://prove2.me/submissions/ab52eefa-8382-4aed-b405-f7d27a38c2b5

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
lemma S170bF_tc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (z : List R) (q : Polynomial R) :
    tvec1 z q = Matrix.vecMul (cvec1 z q) ctmat1 := by
  obtain ⟨h1, h2, h3⟩ := S170bF_main z q
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, ctmat1, tvec1, cvec1, h1, h2, h3] <;> ring


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (z : List R) (q : Polynomial R) :
    Matrix.det ctmat1 = 2 ∧
    cvec1 z q = Matrix.vecMul (tvec1 z q) ctmat1⁻¹ ∧
    (constraints1 z q 1 : ℚ) = ((taq z q : ℚ) + (taq z (q ^ 2) : ℚ)) / 2 := by
  have hdet : Matrix.det ctmat1 = 2 := by
    simp [Matrix.det_fin_three, ctmat1]; norm_num
  refine ⟨hdet, ?_, ?_⟩
  · rw [S170bF_tc z q, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_iff_ne_zero.2 (by norm_num)),
      Matrix.vecMul_one]
  · obtain ⟨h1, h2, h3⟩ := S170bF_main z q
    rw [h1, h2]; push_cast; ring

end
