-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.Supplement.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:18:10.650657+00:00
-- url     : https://prove2.me/submissions/a1aab03a-96a5-405c-8bbc-b689896cf9a7

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive
open SubadditiveMMS580.Amplification.Supplement

theorem SMMSB1_final (x D : ℝ) (hx : 1 ≤ x) (hD : 2 ≤ D) (hxD : x < D)
    (key : D * (2 * D - 1) ≤ (D - x) * (11 * x - 5)) :
    1 / (11 * x - 5) ≤ Fd D x := by
  unfold Fd
  have hpos : 0 < 1 - x / D := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hxD
  rw [max_eq_left hpos.le]
  have h1 : 0 < 11 * x - 5 := by linarith
  have h2 : 0 < 2 * D - 1 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  have : 1 - x / D = (D - x) / D := by field_simp
  rw [this, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

theorem solution (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (hk : 1 ≤ k)
    (hle : x ≤ xd ((2 : ℝ) ^ k))
    (hfirst : ∀ k' : ℕ, 1 ≤ k' → k' < k → xd ((2 : ℝ) ^ k') < x) :
    1 / (11 * x - 5) ≤ Fd ((2 : ℝ) ^ k) x := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · unfold xd at hle
    norm_num at hle
    rw [pow_one]
    apply SMMSB1_final x 2 hx (by norm_num) (by linarith)
    nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hf := hfirst j (by omega) (by omega)
    set E : ℝ := (2:ℝ) ^ j with hE
    have hE2 : 2 ≤ E := by
      rw [hE]
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    have hDk : (2:ℝ) ^ (j+1) = 2 * E := by rw [pow_succ, hE]; ring
    rw [hDk] at hle ⊢
    unfold xd at hle hf
    have h6 : 0 < 6 * E - 1 := by linarith
    have h12 : 0 < 6 * (2 * E) - 1 := by linarith
    rw [div_lt_iff₀ h6] at hf
    rw [le_div_iff₀ h12] at hle
    have hxD : x < 2 * E := by nlinarith
    apply SMMSB1_final x (2 * E) hx (by linarith) hxD
    set D : ℝ := 2 * E with hDdef
    have hD4 : 4 ≤ D := by linarith
    set a : ℝ := x * (3 * D - 1) - D ^ 2 with ha
    set b : ℝ := 4 * D ^ 2 - x * (6 * D - 1) with hb
    have ha0 : 0 ≤ a := by rw [ha, hDdef]; nlinarith
    have hb0 : 0 ≤ b := by rw [hb]; linarith
    have hid : 3 * D * (3 * D - 1) * (6 * D - 1) * ((D - x) * (11 * x - 5) - D * (2 * D - 1))
        = 33 * D * (a * b) + (2 * D - 1) * (D - 4) * (6 * D - 1) * b
          + 2 * (4 * D - 1) * (D - 2) * (3 * D - 1) * a := by
      rw [ha, hb]; ring
    have hK : 0 < 3 * D * (3 * D - 1) * (6 * D - 1) := by
      apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have hR : 0 ≤ 33 * D * (a * b) + (2 * D - 1) * (D - 4) * (6 * D - 1) * b
          + 2 * (4 * D - 1) * (D - 2) * (3 * D - 1) * a := by
      have h1 : 0 ≤ 33 * D * (a * b) := mul_nonneg (by linarith) (mul_nonneg ha0 hb0)
      have h2 : 0 ≤ (2 * D - 1) * (D - 4) * (6 * D - 1) * b :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hb0
      have h3 : 0 ≤ 2 * (4 * D - 1) * (D - 2) * (3 * D - 1) * a :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) ha0
      linarith
    rw [← hid] at hR
    have := nonneg_of_mul_nonneg_right (by linarith [hR] : 0 ≤ (3 * D * (3 * D - 1) * (6 * D - 1)) * ((D - x) * (11 * x - 5) - D * (2 * D - 1))) hK
    linarith
