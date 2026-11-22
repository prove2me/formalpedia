-- Prove2me | solution 1 for SZ.quadPisot_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:58:35.377557+00:00
-- url     : https://prove2.me/submissions/74bca7f7-5832-464d-bd7d-0a8aea6d8af5

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
import Theorems.Thm_SZ_Pair_neg_one_lt_beta
import Theorems.Thm_SZ_Pair_sq_alpha
import Theorems.Thm_SZ_mem_MahlerZ_of_neg
import Theorems.Thm_SZ_mem_MahlerZ_of_pos
import Theorems.Thm_SZ_mem_MahlerZ_of_three_le
import Theorems.Thm_SZ_oneAddSqrtThree_mem_MahlerZ


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution {α : ℝ} (h : IsQuadPisot α) (hne : α ≠ golden) :
    α ∈ MahlerZ := by
  obtain ⟨hα1, β, a, b, hβ0, hβabs, hsum, hprod⟩ := h
  have hp : Pair α β a b := ⟨hα1, hβabs, hsum, hprod⟩
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα1
  rcases lt_trichotomy β 0 with hneg | hzero | hpos
  · -- the negative-conjugate family: `1 ≤ b ≤ a`
    have hβgt : -1 < β := hp.neg_one_lt_beta
    have hbpos : 0 < b := by
      have h1 : -(b : ℝ) < 0 := by rw [← hprod]; exact mul_neg_of_pos_of_neg hα0 hneg
      have h2 : (0 : ℝ) < (b : ℝ) := by linarith
      exact_mod_cast h2
    have hapos : 0 < a := by
      have h2 : (0 : ℝ) < (a : ℝ) := by rw [← hsum]; linarith
      exact_mod_cast h2
    have hba : b ≤ a := by
      have hmul : (0 : ℝ) < (1 + α) * (1 + β) :=
        mul_pos (by linarith) (by linarith)
      have hkey : (0 : ℝ) < 1 + (a : ℝ) - (b : ℝ) := by nlinarith [hsum, hprod]
      have h2 : (0 : ℤ) < 1 + a - b := by exact_mod_cast hkey
      omega
    rcases (by omega : a = 1 ∨ a = 2 ∨ 3 ≤ a) with ha | ha | ha
    · -- `a = 1`, hence `b = 1` and `α` is the golden mean
      exfalso
      have hb1 : b = 1 := by omega
      subst ha; subst hb1
      have hsq : α ^ 2 = α + 1 := by have := hp.sq_alpha; push_cast at this; linarith
      have h5 : (2 * α - 1) ^ 2 = 5 := by nlinarith
      have hroot : 2 * α - 1 = Real.sqrt 5 := by
        rw [← h5, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * α - 1)]
      exact hne (by rw [golden, ← hroot]; ring)
    · -- `a = 2`, so `b = 1` (Theorem A) or `b = 2` (`1 + √3`)
      subst ha
      rcases (by omega : b = 1 ∨ b = 2) with hb | hb
      · subst hb
        exact mem_MahlerZ_of_neg hp hneg ⟨1, by ring⟩ (by rintro ⟨k, hk⟩; omega)
      · subst hb
        have hsq : α ^ 2 = 2 * α + 2 := by have := hp.sq_alpha; push_cast at this; linarith
        have h3 : (α - 1) ^ 2 = 3 := by nlinarith
        have hroot : α - 1 = Real.sqrt 3 := by
          rw [← h3, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ α - 1)]
        have : α = 1 + Real.sqrt 3 := by linarith
        rw [this]; exact oneAddSqrtThree_mem_MahlerZ
    · -- `a ≥ 3`, so `α > 3`: Tijdeman
      have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      exact mem_MahlerZ_of_three_le (by linarith [hsum])
  · exact absurd hzero hβ0
  · exact mem_MahlerZ_of_pos hp hpos
end SZ
