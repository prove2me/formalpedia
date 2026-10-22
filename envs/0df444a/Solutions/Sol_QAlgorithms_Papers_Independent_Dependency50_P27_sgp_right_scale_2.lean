-- Prove2me | solution 2 for QAlgorithms.Papers.Independent.Dependency50.P27.sgp_right_scale
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:28:51.592394+00:00
-- url     : https://prove2.me/submissions/67033bb5-d4d4-4a22-b80d-23f16f4c5288

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

set_option autoImplicit false

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27

theorem sgr_mul_aux {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R] [IsStrictOrderedRing R]
    (c y : R) : sgr (c * y) = sgr c * sgr y := by
  unfold sgr
  by_cases hc : c = 0
  · simp [hc]
  by_cases hy : y = 0
  · simp [hy]
  have hcy : c * y ≠ 0 := mul_ne_zero hc hy
  simp only [hc, hy, hcy, if_false]
  rcases lt_or_gt_of_ne hc with hc' | hc' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · have : 0 < c * y := mul_pos_of_neg_of_neg hc' hy'
    simp [not_lt.mpr hc'.le, not_lt.mpr hy'.le, this]
  · have : ¬ 0 < c * y := not_lt.mpr (mul_neg_of_neg_of_pos hc' hy').le
    simp [not_lt.mpr hc'.le, hy', this]
  · have : ¬ 0 < c * y := not_lt.mpr (mul_neg_of_pos_of_neg hc' hy').le
    simp [hc', not_lt.mpr hy'.le, this]
  · have : 0 < c * y := mul_pos hc' hy'
    simp [hc', hy', this]

theorem firstSign_scale (c : ℤ) (hc : c = 0 ∨ c = 1 ∨ c = -1) (l : List ℤ) :
    firstSign (l.map (fun s => c * s)) = c * firstSign l := by
  induction l with
  | nil => simp [firstSign]
  | cons s ss ih =>
    simp only [List.map_cons, firstSign]
    rcases hc with rfl | rfl | rfl
    · simp only [zero_mul] at ih ⊢
      simp only [firstSign, if_true]
      exact ih
    · simpa using ih
    · simp only [neg_mul, one_mul, neg_one_mul] at ih ⊢
      by_cases hs : s = 0
      · simp [hs, ih]
      · simp [hs]

theorem sgr_cases {R : Type*} [CommRing R] [LinearOrder R] (c : R) :
    sgr c = 0 ∨ sgr c = 1 ∨ sgr c = -1 := by
  unfold sgr; split_ifs <;> simp

theorem iter_deriv_smul {R : Type*} [CommRing R] (c : R) (p : Polynomial R) (k : ℕ) :
    ((Polynomial.derivative : Polynomial R → Polynomial R)^[k]) (c • p)
      = c • ((Polynomial.derivative : Polynomial R → Polynomial R)^[k]) p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Polynomial.derivative_smul, ih]

theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (c : R) (p : Polynomial R) (x : R) :
    rightSign (c • p) x = sgr c * rightSign p x := by
  by_cases hc : c = 0
  · subst hc
    simp [rightSign, sgr, firstSign]
  · unfold rightSign
    have hdeg : (c • p).natDegree = p.natDegree := Polynomial.natDegree_smul p hc
    rw [hdeg]
    have : ∀ k, sgr ((((Polynomial.derivative : Polynomial R → Polynomial R)^[k]) (c • p)).eval x)
        = sgr c * sgr ((((Polynomial.derivative : Polynomial R → Polynomial R)^[k]) p).eval x) := by
      intro k
      rw [iter_deriv_smul, Polynomial.eval_smul, smul_eq_mul, sgr_mul_aux]
    simp only [this]
    rw [← firstSign_scale (sgr c) (sgr_cases c)]
    simp [List.map_map, Function.comp_def]
