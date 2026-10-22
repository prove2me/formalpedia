-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.sgp_right_scale
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:56:21.979882+00:00
-- url     : https://prove2.me/submissions/88f65383-7e95-4bd6-b275-76192d909ba9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

set_option autoImplicit false

namespace QAlgorithms.Papers.Independent.Dependency50.P27

theorem sgr_mul_aux28b {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (a b : R) :
    sgr (a * b) = sgr a * sgr b := by
  rcases lt_trichotomy a 0 with ha | ha | ha <;>
  rcases lt_trichotomy b 0 with hb | hb | hb
  · have h : 0 < a * b := mul_pos_of_neg_of_neg ha hb
    simp [sgr, ha.ne, hb.ne, h.ne', h, not_lt.mpr ha.le, not_lt.mpr hb.le]
  · subst hb; simp [sgr]
  · have h : a * b < 0 := mul_neg_of_neg_of_pos ha hb
    simp [sgr, ha.ne, hb.ne', h.ne, not_lt.mpr h.le, not_lt.mpr ha.le, hb]
  · subst ha; simp [sgr]
  · subst ha; simp [sgr]
  · subst ha; simp [sgr]
  · have h : a * b < 0 := mul_neg_of_pos_of_neg ha hb
    simp [sgr, ha.ne', hb.ne, h.ne, not_lt.mpr h.le, not_lt.mpr hb.le, ha]
  · subst hb; simp [sgr]
  · have h : 0 < a * b := mul_pos ha hb
    simp [sgr, ha.ne', hb.ne', h.ne', h, ha, hb]

theorem firstSign_map_mul_aux28b (k : ℤ) (hk : k ≠ 0) (l : List ℤ) :
    firstSign (l.map (fun s => k * s)) = k * firstSign l := by
  induction l with
  | nil => simp [firstSign]
  | cons s ss ih =>
    simp only [List.map_cons, firstSign, mul_eq_zero, hk, false_or]
    by_cases hs : s = 0
    · simp [hs, ih]
    · simp [hs]

end QAlgorithms.Papers.Independent.Dependency50.P27

open QAlgorithms.Papers.Independent.Dependency50.P27 Polynomial in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (c : R) (p : Polynomial R) (x : R) :
    rightSign (c • p) x = sgr c * rightSign p x := by
  by_cases hc : c = 0
  · subst hc
    simp [rightSign, sgr, firstSign]
  · have hsc : sgr c ≠ 0 := by
      simp only [sgr, hc, if_false]; split_ifs <;> decide
    unfold rightSign
    rw [natDegree_smul p hc, ← firstSign_map_mul_aux28b _ hsc, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, iterate_derivative_smul, eval_smul, smul_eq_mul, sgr_mul_aux28b]
