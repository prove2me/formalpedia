-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P94.binaryConditionalEntropy_S7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:47:41.370641+00:00
-- url     : https://prove2.me/submissions/776b9133-f341-4825-8ab4-336149ac2bf7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P94

open MeasureTheory
open scoped ComplexConjugate

namespace Aux_P94S7

lemma core (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : a + b + (c + d) = 1) :
    (if a + b = 0 then 0 else (a + b) * Real.binEntropy (a / (a + b))) +
      (if c + d = 0 then 0 else (c + d) * Real.binEntropy (c / (c + d))) ≤
      Real.binEntropy (b + c) := by
  set et : ℝ := if a + b = 0 then 0 else b / (a + b) with het
  set ef : ℝ := if c + d = 0 then 0 else c / (c + d) with hef
  have h1 : (if a + b = 0 then 0 else (a + b) * Real.binEntropy (a / (a + b))) =
      (a + b) * Real.binEntropy et := by
    by_cases h : a + b = 0
    · rw [if_pos h, h, zero_mul]
    · rw [if_neg h, het, if_neg h]
      congr 1
      rw [← Real.binEntropy_one_sub (b / (a + b))]
      congr 1
      field_simp
      ring
  have h2 : (if c + d = 0 then 0 else (c + d) * Real.binEntropy (c / (c + d))) =
      (c + d) * Real.binEntropy ef := by
    by_cases h : c + d = 0
    · rw [if_pos h, h, zero_mul]
    · rw [if_neg h, hef, if_neg h]
  have h3 : (a + b) * et = b := by
    by_cases h : a + b = 0
    · rw [het, if_pos h, mul_zero]; linarith
    · rw [het, if_neg h]; field_simp
  have h4 : (c + d) * ef = c := by
    by_cases h : c + d = 0
    · rw [hef, if_pos h, mul_zero]; linarith
    · rw [hef, if_neg h]; field_simp
  have hmt : et ∈ Set.Icc (0:ℝ) 1 := by
    by_cases h : a + b = 0
    · rw [het, if_pos h]; exact ⟨le_rfl, zero_le_one⟩
    · rw [het, if_neg h]
      have hpos : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm h)
      exact ⟨div_nonneg hb hpos.le, (div_le_one hpos).mpr (by linarith)⟩
  have hmf : ef ∈ Set.Icc (0:ℝ) 1 := by
    by_cases h : c + d = 0
    · rw [hef, if_pos h]; exact ⟨le_rfl, zero_le_one⟩
    · rw [hef, if_neg h]
      have hpos : 0 < c + d := lt_of_le_of_ne (by linarith) (Ne.symm h)
      exact ⟨div_nonneg hc hpos.le, (div_le_one hpos).mpr (by linarith)⟩
  have hcc := Real.strictConcave_binEntropy.concaveOn.2 hmt hmf (by linarith : 0 ≤ a + b)
    (by linarith : 0 ≤ c + d) hs
  simp only [smul_eq_mul, h3, h4] at hcc
  rw [h1, h2]
  exact hcc

end Aux_P94S7

open QAlgorithms.Papers.Independent.Intakethird100.P94 Aux_P94S7 in
theorem solution (P : Bool → Bool → ℝ)
    (hNonneg : ∀ a b, 0 ≤ P a b)
    (hTotal : ∑ a : Bool, ∑ b : Bool, P a b = 1) :
    conditionalEntropyBits P ≤ QAlgorithms.binEntropy2 (binaryError P) := by
  have herr : binaryError P = P true false + P false true := by
    unfold binaryError
    simp only [Fintype.sum_bool, ne_eq, not_true_eq_false, if_false, Bool.true_eq_false,
      Bool.false_eq_true, not_false_eq_true, if_true, zero_add, add_zero]
  have hs : P true true + P true false + (P false true + P false false) = 1 := by
    rw [← hTotal]; simp only [Fintype.sum_bool]
  have hcore := core (P true true) (P true false) (P false true) (P false false)
    (hNonneg _ _) (hNonneg _ _) (hNonneg _ _) (hNonneg _ _) hs
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrow : ∀ r y : ℝ, (if r = 0 then 0 else r * QAlgorithms.binEntropy2 y) =
      (if r = 0 then 0 else r * Real.binEntropy y) / Real.log 2 := by
    intro r y
    unfold QAlgorithms.binEntropy2
    split_ifs
    · rw [zero_div]
    · rw [mul_div_assoc]
  unfold conditionalEntropyBits
  rw [herr]
  simp only [Fintype.sum_bool]
  rw [hrow, hrow, ← add_div]
  unfold QAlgorithms.binEntropy2
  exact div_le_div_of_nonneg_right (by linarith [hcore]) hL.le
