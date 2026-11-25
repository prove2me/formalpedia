-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_filter_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:03.537551+00:00
-- url     : https://prove2.me/submissions/0d5abbc5-12ba-4c8f-915e-760e7bdda32d

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_card_adt_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_card_filter_zero_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_filter_zero_eq_empty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n : ℕ) (hn : 1 ≤ n) (P : ℝ) (hP : 0 ≤ P)
    (hb : ∀ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ (2 + (D : ℝ)) * n * P) :
    ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ 3 ^ D * (2 + (D : ℝ)) * P * (n : ℝ) ^ D := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hcard : ((((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
      * n ≤ 3 ^ D * (n : ℝ) ^ D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      rw [chiPAux_filter_zero_eq_empty]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
      have h1 : ((((Finset.Nat.antidiagonalTuple (k + 1 + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
          ≤ ((n : ℝ) + 1 + 1) ^ k := by
        have := (chiPAux_card_filter_zero_le (k + 1) n).trans (chiPAux_card_adt_le k (n + 1))
        exact_mod_cast this
      have h2 : ((n : ℝ) + 1 + 1) ^ k ≤ (3 * (n : ℝ)) ^ k := by
        gcongr
        linarith
      have h3 : (0 : ℝ) ≤ 3 ^ k * (n : ℝ) ^ (k + 1) := by positivity
      calc ((((Finset.Nat.antidiagonalTuple (k + 1 + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
            * n ≤ (3 * (n : ℝ)) ^ k * n := mul_le_mul_of_nonneg_right (h1.trans h2) hn0
        _ = 3 ^ k * (n : ℝ) ^ (k + 1) := by ring
        _ ≤ 3 ^ (k + 1) * (n : ℝ) ^ (k + 1) := by
          have e : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
          rw [e]
          linarith
  have hsum := Finset.sum_le_sum hb
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hP0 : 0 ≤ (2 + (D : ℝ)) * P := mul_nonneg (by linarith) hP
  refine hsum.trans ?_
  calc ((((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
        * ((2 + (D : ℝ)) * n * P)
      = (((((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
          * n) * ((2 + (D : ℝ)) * P) := by ring
    _ ≤ (3 ^ D * (n : ℝ) ^ D) * ((2 + (D : ℝ)) * P) := mul_le_mul_of_nonneg_right hcard hP0
    _ = 3 ^ D * (2 + (D : ℝ)) * P * (n : ℝ) ^ D := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
