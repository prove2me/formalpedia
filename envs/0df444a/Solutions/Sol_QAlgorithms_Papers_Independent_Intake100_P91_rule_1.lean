-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P91.rule_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:56:09.737017+00:00
-- url     : https://prove2.me/submissions/71750e93-cf97-4be6-b99d-4ac2fca71ec3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Intake100.P91 in
theorem solution (n a b : ℕ) (hn : 1 ≤ n) (ha : a ≤ n-1)
    (hb : b ≤ n) (hedge : b = a ∨ b = a+1) :
    qubitLouck (n-1) 0 a n 0 b =
      if a = b then Real.sqrt (((n : ℝ) - b) / (n : ℝ))
      else Real.sqrt ((b : ℝ) / (n : ℝ)) := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have htau : (fun j : ℕ => if j = 1 then 1 else if n = n - 1 + 1 ∧ 0 = 0 then 1 else 2) =
      fun _ => 1 := by
    funext j; by_cases hj : j = 1 <;> simp [hj, hn1]
  have e1 : (Finset.Icc 1 2).erase 1 = ({2} : Finset ℕ) := by ext x; simp <;> omega
  have e2 : (Finset.Icc 1 1).erase 1 = (∅ : Finset ℕ) := by ext x; simp
  have e3 : Finset.Icc (2 + 1) 2 = (∅ : Finset ℕ) := by ext x; simp <;> omega
  have e4 : Finset.Icc 1 (2 - 1) = ({1} : Finset ℕ) := by ext x; simp <;> omega
  have e5 : Finset.Icc (1 + 1) 2 = ({2} : Finset ℕ) := by ext x; simp <;> omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  have ha' : (a : ℝ) ≤ n - 1 := by rw [← hcast]; exact_mod_cast ha
  rcases hedge with rfl | rfl
  · rw [if_pos rfl]
    unfold qubitLouck
    rw [if_pos rfl, htau]
    unfold louck
    rw [e3, Finset.prod_empty, one_mul, if_neg (by norm_num), e4, Finset.prod_singleton,
      show (2 : ℕ) - 1 = 1 from rfl, show ((Finset.Icc 1 2).erase 1) = ({2} : Finset ℕ) from e1,
      Finset.prod_singleton]
    simp only [partialHook, qubitGT]
    norm_num [hcast]
    rw [show (n : ℝ) - 1 + 2 - 1 = n by ring, abs_of_nonneg (div_nonneg (by linarith) hn0.le),
      Real.sqrt_div' _ hn0.le]
  · rw [if_neg (by omega)]
    unfold qubitLouck
    rw [if_neg (by omega), htau]
    unfold louck
    rw [e5, Finset.prod_singleton, if_pos rfl, mul_one, show (2 : ℕ) - 1 = 1 from rfl, e1, e2,
      Finset.prod_empty, Finset.prod_singleton]
    simp only [partialHook, qubitGT, comparisonSign]
    norm_num [hcast]
    rw [show (n : ℝ) - 1 + 2 - 1 = n by ring, abs_of_nonneg (div_nonneg (by positivity) hn0.le),
      Real.sqrt_div' _ hn0.le]
