-- Prove2me | solution 1 for ThomsonProblem.thomson_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:11:21.685626+00:00
-- url     : https://prove2.me/submissions/cb08b4dd-0538-4c29-b020-29ab2cdf16e8

import Mathlib
import Definitions.Def_ThomsonProblem_defs

lemma key_ineq_d6a4fd35 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 ≤ 9) : Real.sqrt 3 ≤ 1 / a + 1 / b + 1 / c := by
  set s := 1 / a + 1 / b + 1 / c with hs
  have hs0 : 0 ≤ s := by positivity
  have hst : 9 ≤ s * (a + b + c) := by
    have e : s * (a + b + c) = (b * c + a * c + a * b) * (a + b + c) / (a * b * c) := by
      rw [hs]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg ha.le (sq_nonneg (b - c)), mul_nonneg hb.le (sq_nonneg (a - c)),
      mul_nonneg hc.le (sq_nonneg (a - b))]
  have ht : (a + b + c) ^ 2 ≤ 27 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have htpos : 0 < a + b + c := by positivity
  have hs2 : 3 ≤ s ^ 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have h81 : 81 ≤ (s * (a + b + c)) ^ 2 := by nlinarith
    have : (s * (a + b + c)) ^ 2 = s ^ 2 * (a + b + c) ^ 2 := by ring
    have hpos2 : 0 < (a + b + c) ^ 2 := by positivity
    nlinarith
  calc Real.sqrt 3 ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hs2
    _ = s := Real.sqrt_sq hs0

open ThomsonProblem in
lemma energy_three_d6a4fd35 (x : Fin 3 → Space) :
    coulombEnergy x = 1 / dist (x 0) (x 1) + 1 / dist (x 0) (x 2) + 1 / dist (x 1) (x 2) := by
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  simp [coulombEnergy, Fin.sum_univ_three, h0, h1, h2]

open ThomsonProblem in
lemma sumsq_le_d6a4fd35 (y : Fin 3 → Space) (hn : ∀ i, ‖y i‖ = 1) :
    dist (y 0) (y 1) ^ 2 + dist (y 0) (y 2) ^ 2 + dist (y 1) (y 2) ^ 2 ≤ 9 := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have h01 := norm_sub_sq_real (y 0) (y 1)
  have h02 := norm_sub_sq_real (y 0) (y 2)
  have h12 := norm_sub_sq_real (y 1) (y 2)
  have hs := norm_add_sq_real (y 0 + y 1) (y 2)
  have hs2 := norm_add_sq_real (y 0) (y 1)
  have hi := inner_add_left (𝕜 := ℝ) (y 0) (y 1) (y 2)
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hnn := sq_nonneg ‖y 0 + y 1 + y 2‖
  rw [hn0, hn1] at h01 hs2
  rw [hn0, hn2] at h02
  rw [hn1, hn2] at h12
  rw [hn2] at hs
  nlinarith

open ThomsonProblem in
lemma tri_dist01_d6a4fd35 : dist (equilateralTriangle 0) (equilateralTriangle 1) = Real.sqrt 3 := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  simp [equilateralTriangle, Fin.sum_univ_three, Real.dist_eq, sq_abs] <;> nlinarith

open ThomsonProblem in
lemma tri_dist02_d6a4fd35 : dist (equilateralTriangle 0) (equilateralTriangle 2) = Real.sqrt 3 := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  simp [equilateralTriangle, Fin.sum_univ_three, Real.dist_eq, sq_abs] <;> nlinarith

open ThomsonProblem in
lemma tri_dist12_d6a4fd35 : dist (equilateralTriangle 1) (equilateralTriangle 2) = Real.sqrt 3 := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  simp [equilateralTriangle, Fin.sum_univ_three, Real.dist_eq, sq_abs] <;> nlinarith

open ThomsonProblem in
lemma tri_norm_d6a4fd35 (i : Fin 3) : ‖equilateralTriangle i‖ = 1 := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  fin_cases i <;>
    simp [equilateralTriangle, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs] <;>
    (try rw [Real.sqrt_eq_one]) <;> nlinarith

open ThomsonProblem in
theorem solution : IsEnergyMinimizer equilateralTriangle := by
  have hE : coulombEnergy equilateralTriangle = Real.sqrt 3 := by
    rw [energy_three_d6a4fd35, tri_dist01_d6a4fd35, tri_dist02_d6a4fd35, tri_dist12_d6a4fd35]
    have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have hp : 0 < Real.sqrt 3 := by positivity
    field_simp
    nlinarith
  have hpos : 0 < Real.sqrt 3 := by positivity
  have n01 : equilateralTriangle 0 ≠ equilateralTriangle 1 := fun h => by
    have hd := tri_dist01_d6a4fd35
    rw [h, dist_self] at hd
    linarith
  have n02 : equilateralTriangle 0 ≠ equilateralTriangle 2 := fun h => by
    have hd := tri_dist02_d6a4fd35
    rw [h, dist_self] at hd
    linarith
  have n12 : equilateralTriangle 1 ≠ equilateralTriangle 2 := fun h => by
    have hd := tri_dist12_d6a4fd35
    rw [h, dist_self] at hd
    linarith
  refine ⟨⟨tri_norm_d6a4fd35, ?_⟩, fun y hy => ?_⟩
  · intro a b hab
    match a, b with
    | 0, 0 => rfl
    | 1, 1 => rfl
    | 2, 2 => rfl
    | 0, 1 => exact absurd hab n01
    | 0, 2 => exact absurd hab n02
    | 1, 2 => exact absurd hab n12
    | 1, 0 => exact absurd hab.symm n01
    | 2, 0 => exact absurd hab.symm n02
    | 2, 1 => exact absurd hab.symm n12
  · rw [hE, energy_three_d6a4fd35]
    obtain ⟨hn, hinj⟩ := hy
    have p01 : 0 < dist (y 0) (y 1) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p02 : 0 < dist (y 0) (y 2) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    have p12 : 0 < dist (y 1) (y 2) := dist_pos.mpr (fun h => absurd (hinj h) (by decide))
    exact key_ineq_d6a4fd35 _ _ _ p01 p02 p12 (sumsq_le_d6a4fd35 y hn)
