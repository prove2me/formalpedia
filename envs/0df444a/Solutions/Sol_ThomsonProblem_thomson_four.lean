-- Prove2me | solution 1 for ThomsonProblem.thomson_four
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:35:54.699983+00:00
-- url     : https://prove2.me/submissions/d8a97502-0a80-4d9a-b547-adba247cd90d

import Mathlib
import Definitions.Def_ThomsonProblem_defs

lemma tangent_9b304ed3 (d : ℝ) (hd : 0 < d) :
    3 * Real.sqrt 6 / 64 * (8 - d ^ 2) ≤ 1 / d := by
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hs : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  rw [le_div_iff₀ hd]
  nlinarith [mul_nonneg (sq_nonneg (d - 2 * Real.sqrt 6 / 3))
    (show 0 ≤ d + 4 * Real.sqrt 6 / 3 by positivity)]

open ThomsonProblem in
lemma energy_four_9b304ed3 (x : Fin 4 → Space) :
    coulombEnergy x = 1 / dist (x 0) (x 1) + 1 / dist (x 0) (x 2) + 1 / dist (x 0) (x 3)
      + 1 / dist (x 1) (x 2) + 1 / dist (x 1) (x 3) + 1 / dist (x 2) (x 3) := by
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  simp [coulombEnergy, Fin.sum_univ_four, h0, h1, h2, h3]
  ring

open ThomsonProblem in
lemma sumsq_le_9b304ed3 (y : Fin 4 → Space) (hn : ∀ i, ‖y i‖ = 1) :
    dist (y 0) (y 1) ^ 2 + dist (y 0) (y 2) ^ 2 + dist (y 0) (y 3) ^ 2
      + dist (y 1) (y 2) ^ 2 + dist (y 1) (y 3) ^ 2 + dist (y 2) (y 3) ^ 2 ≤ 16 := by
  simp only [dist_eq_norm]
  have h01 := norm_sub_sq_real (y 0) (y 1)
  have h02 := norm_sub_sq_real (y 0) (y 2)
  have h03 := norm_sub_sq_real (y 0) (y 3)
  have h12 := norm_sub_sq_real (y 1) (y 2)
  have h13 := norm_sub_sq_real (y 1) (y 3)
  have h23 := norm_sub_sq_real (y 2) (y 3)
  have hs4 := norm_add_sq_real (y 0 + y 1 + y 2) (y 3)
  have hs3 := norm_add_sq_real (y 0 + y 1) (y 2)
  have hs2 := norm_add_sq_real (y 0) (y 1)
  have hi3a := inner_add_left (𝕜 := ℝ) (y 0 + y 1) (y 2) (y 3)
  have hi3b := inner_add_left (𝕜 := ℝ) (y 0) (y 1) (y 3)
  have hi2 := inner_add_left (𝕜 := ℝ) (y 0) (y 1) (y 2)
  have hnn := sq_nonneg ‖y 0 + y 1 + y 2 + y 3‖
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hn3 := hn 3
  rw [hn0, hn1] at h01 hs2
  rw [hn0, hn2] at h02
  rw [hn0, hn3] at h03
  rw [hn1, hn2] at h12
  rw [hn1, hn3] at h13
  rw [hn2, hn3] at h23
  rw [hn3] at hs4
  rw [hn2] at hs3
  nlinarith

open ThomsonProblem in
lemma tet_sq_9b304ed3 (i j : Fin 4) (h : i ≠ j) :
    dist (regularTetrahedron i) (regularTetrahedron j) ^ 2 = 8 / 3 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h3p : 0 < Real.sqrt 3 := by positivity
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl h) <;>
    simp [regularTetrahedron, Fin.sum_univ_three, Real.dist_eq, sq_abs] <;>
    field_simp <;> nlinarith [h3]

open ThomsonProblem in
lemma tet_dist_9b304ed3 (i j : Fin 4) (h : i ≠ j) :
    dist (regularTetrahedron i) (regularTetrahedron j) = 2 * Real.sqrt 6 / 3 := by
  have hq := tet_sq_9b304ed3 i j h
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hs : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hd : 0 ≤ dist (regularTetrahedron i) (regularTetrahedron j) := dist_nonneg
  nlinarith [sq_nonneg (dist (regularTetrahedron i) (regularTetrahedron j) - 2 * Real.sqrt 6 / 3),
    sq_nonneg (dist (regularTetrahedron i) (regularTetrahedron j) + 2 * Real.sqrt 6 / 3)]

open ThomsonProblem in
lemma tet_norm_9b304ed3 (i : Fin 4) : ‖regularTetrahedron i‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h3p : 0 < Real.sqrt 3 := by positivity
  fin_cases i <;>
    simp [regularTetrahedron, Fin.sum_univ_three, sq_abs] <;>
    field_simp <;> nlinarith

open ThomsonProblem in
theorem solution : IsEnergyMinimizer regularTetrahedron := by
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hs : 0 < Real.sqrt 6 := by positivity
  have hE : coulombEnergy regularTetrahedron = 3 * Real.sqrt 6 / 2 := by
    rw [energy_four_9b304ed3]
    rw [tet_dist_9b304ed3 0 1 (by decide), tet_dist_9b304ed3 0 2 (by decide),
      tet_dist_9b304ed3 0 3 (by decide), tet_dist_9b304ed3 1 2 (by decide),
      tet_dist_9b304ed3 1 3 (by decide), tet_dist_9b304ed3 2 3 (by decide)]
    field_simp
    nlinarith
  refine ⟨⟨tet_norm_9b304ed3, ?_⟩, fun y hy => ?_⟩
  · intro a b hab
    by_contra hne
    have hd := tet_dist_9b304ed3 a b hne
    rw [hab, dist_self] at hd
    linarith
  · rw [hE, energy_four_9b304ed3]
    obtain ⟨hn, hinj⟩ := hy
    have p01 : 0 < dist (y 0) (y 1) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p02 : 0 < dist (y 0) (y 2) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p03 : 0 < dist (y 0) (y 3) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p12 : 0 < dist (y 1) (y 2) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p13 : 0 < dist (y 1) (y 3) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p23 : 0 < dist (y 2) (y 3) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have t01 := tangent_9b304ed3 _ p01
    have t02 := tangent_9b304ed3 _ p02
    have t03 := tangent_9b304ed3 _ p03
    have t12 := tangent_9b304ed3 _ p12
    have t13 := tangent_9b304ed3 _ p13
    have t23 := tangent_9b304ed3 _ p23
    have hsq := sumsq_le_9b304ed3 y hn
    nlinarith
