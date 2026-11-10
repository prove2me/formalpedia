-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P91.rule_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T01:27:40.076388+00:00
-- url     : https://prove2.me/submissions/78d716cc-cd26-46da-9810-b98fd20863f9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Intake100.P91 in
theorem solution (n a b : ℕ) (hn : 2 ≤ n) (ha : a ≤ n-1)
    (hbLower : 1 ≤ b) (hbUpper : b ≤ n-1) (hedge : b = a ∨ b = a+1) :
    qubitLouck (n-1) 0 a (n-1) 1 b =
      if a = b then Real.sqrt ((b : ℝ) / (n : ℝ))
      else -Real.sqrt (((n : ℝ) - b) / (n : ℝ)) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have e3 : Finset.Icc 3 2 = (∅ : Finset ℕ) := by ext x; simp <;> omega
  have e1' : (Finset.Icc 1 2).erase 2 = ({1} : Finset ℕ) := by ext x; simp <;> omega
  have e2 : (Finset.Icc 1 1).erase 1 = (∅ : Finset ℕ) := by ext x; simp
  have e22 : Finset.Icc 2 2 = ({2} : Finset ℕ) := by ext x; simp <;> omega
  rcases hedge with rfl | rfl
  · rw [if_pos rfl]
    unfold qubitLouck
    rw [if_pos rfl]
    norm_num [louck, partialHook, qubitGT, e3, e1', hcast]
    rw [show (1 - ((n : ℝ) - 1 + 2)) = -(n : ℝ) by ring, neg_div_neg_eq,
      abs_of_nonneg (by positivity), Real.sqrt_div' _ hn0.le]
  · rw [if_neg (by omega)]
    unfold qubitLouck
    rw [if_neg (by omega)]
    have hb1 : ((a + 1 : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by rw [← hcast]; exact_mod_cast hbUpper
    norm_num [louck, partialHook, qubitGT, comparisonSign, e22, e1', e2, hcast]
    push_cast at hb1
    rw [show (1 - ((n : ℝ) - 1 + 2)) = -(n : ℝ) by ring,
      show (a : ℝ) - ((n : ℝ) - 1 + 2 - 1) + 1 = -((n : ℝ) - ((a : ℝ) + 1)) by ring,
      neg_div_neg_eq, abs_of_nonneg (div_nonneg (by linarith) hn0.le), Real.sqrt_div' _ hn0.le]
