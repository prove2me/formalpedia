-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.row_coefficient_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:11:19.449296+00:00
-- url     : https://prove2.me/submissions/e844cddd-6b44-4b0c-a594-dfdf3d93a4b7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Remark 6.2, PDF p.6: all the analogous row identities are conclusions,
not added assumptions about the matrix. -/
theorem solution (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (k : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ i l,
      (∑ j, (A i j * B l j + B i j * A l j)) = 0 ∧
      (∑ j, (A i j * A l j + 2 * (B i j * B l j))) =
        (2 : ℤ) ^ k * (if i = l then 1 else 0)) ∧
    (∀ i, (∑ j, A i j * B i j) = 0 ∧
      (∑ j, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsk : (Real.sqrt 2) ^ k * (Real.sqrt 2) ^ k = 2 ^ k := by
    rw [← mul_pow, hs2]
  have hskne : (Real.sqrt 2) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
  have key : ∀ i l,
      (((∑ j, (A i j * A l j + 2 * (B i j * B l j)) : ℤ) : ℝ) +
        (((∑ j, (A i j * B l j + B i j * A l j)) : ℤ) : ℝ) * Real.sqrt 2) =
        (((2 : ℤ) ^ k * (if i = l then 1 else 0) : ℤ) : ℝ) := by
    intro i l
    have h := congrFun (congrFun hU.2.1 i) l
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply, hcoeff] at h
    have h2 : ∑ j, ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) * ((A l j : ℝ) + (B l j : ℝ) * Real.sqrt 2)
        = (2 : ℝ) ^ k * (1 : RealMat) i l := by
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
      rw [sq, hsk]
    push_cast
    rw [Matrix.one_apply] at h2
    rw [← h2, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    linear_combination (-(B i j : ℝ) * (B l j : ℝ)) * hs2
  have split : ∀ i l, (∑ j, (A i j * B l j + B i j * A l j)) = 0 ∧
      (∑ j, (A i j * A l j + 2 * (B i j * B l j))) = (2 : ℤ) ^ k * (if i = l then 1 else 0) := by
    intro i l
    have h := key i l
    set P := (∑ j, (A i j * B l j + B i j * A l j))
    set Q := (∑ j, (A i j * A l j + 2 * (B i j * B l j)))
    set R := (2 : ℤ) ^ k * (if i = l then 1 else 0)
    have hP : P = 0 := by
      by_contra hP
      apply irrational_sqrt_two
      refine ⟨((R - Q : ℤ) : ℚ) / (P : ℚ), ?_⟩
      have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP
      push_cast
      field_simp
      linarith
    refine ⟨hP, ?_⟩
    rw [hP] at h
    push_cast at h
    exact_mod_cast (by linarith : (Q : ℝ) = R)
  refine ⟨split, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := split i i
  simp only [if_true, mul_one] at h2
  refine ⟨?_, ?_⟩
  · have : (∑ j, (A i j * B i j + B i j * A i j)) = 2 * ∑ j, A i j * B i j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    omega
  · rw [← h2]; apply Finset.sum_congr rfl; intro j _; ring


end
