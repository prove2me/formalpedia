-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.column_coefficient_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:55:25.40414+00:00
-- url     : https://prove2.me/submissions/f6f369a6-a925-4cf4-bd3d-19e40bc1ab47

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true


theorem g73p_irr (x y : ℤ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have : Real.sqrt 2 = ((-x / y : ℚ) : ℝ) := by
      push_cast; field_simp; linarith
    exact irrational_sqrt_two ⟨_, this.symm⟩

theorem g73p_col (U : RealMat) (hU : SpecialOrthogonal U)
    (k : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsk : Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = (2 : ℝ) ^ k := by
    rw [← mul_pow, ← sq, hs2]
  have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
  intro j l
  have key : (∑ i, U i j * U i l) = if j = l then 1 else 0 := by
    have := congrFun (congrFun hU.1 j) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have e : ∀ i, U i j * U i l = (((A i j * A i l + 2 * (B i j * B i l) : ℤ) : ℝ) +
      ((A i j * B i l + B i j * A i l : ℤ) : ℝ) * Real.sqrt 2) / 2 ^ k := by
    intro i
    rw [hcoeff, hcoeff, div_mul_div_comm, hsk]
    congr 1
    push_cast
    linear_combination ((B i j : ℝ) * B i l) * hs2
  have hsum : (∑ i, U i j * U i l) =
      ((((∑ i, (A i j * A i l + 2 * (B i j * B i l))) : ℤ) : ℝ) +
        (((∑ i, (A i j * B i l + B i j * A i l)) : ℤ) : ℝ) * Real.sqrt 2) / 2 ^ k := by
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_div]
    congr 1
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [key] at hsum
  have h3 : ((((∑ i, (A i j * A i l + 2 * (B i j * B i l))) - 2 ^ k * (if j = l then 1 else 0) : ℤ) : ℝ) +
        (((∑ i, (A i j * B i l + B i j * A i l)) : ℤ) : ℝ) * Real.sqrt 2) = 0 := by
    have := hsum
    field_simp at this
    push_cast at this ⊢
    split_ifs at this ⊢ <;> linarith
  obtain ⟨h4, h5⟩ := g73p_irr _ _ h3
  exact ⟨h5, by linarith⟩

theorem g73p_colfull (U : RealMat) (hU : SpecialOrthogonal U)
    (k : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) ∧
    (∀ j, (∑ i, A i j * B i j) = 0 ∧
      (∑ i, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by
  have H := g73p_col U hU k A B hcoeff
  refine ⟨H, fun j => ?_⟩
  obtain ⟨h1, h2⟩ := H j j
  constructor
  · have : (∑ i, (A i j * B i j + B i j * A i j)) = 2 * ∑ i, A i j * B i j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    omega
  · simp only [if_true, mul_one] at h2
    rw [← h2]; exact Finset.sum_congr rfl (fun i _ => by ring)


/-- Lemma 6.1, PDF p.6, equations (14)-(17). A and B package (a,c,e) and (b,d,f)
by column. No minimality of k is assumed. All conclusions are integer identities. -/
theorem solution (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (k : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) ∧
    (∀ j, (∑ i, A i j * B i j) = 0 ∧
      (∑ i, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by
  exact g73p_colfull U hU k A B hcoeff


end
