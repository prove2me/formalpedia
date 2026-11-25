-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.exists_chiP_succ_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:53.030799+00:00
-- url     : https://prove2.me/submissions/9ecedf65-7bfe-4b6a-82d6-05faeb1b0776

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_card_adt_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiP_succ_sub_eq
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_step_mem
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_monoNormSq_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_filter_zero_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open Finset
private theorem log_add_add_one_le_log_add_log (n D : ℕ) :
    Real.log ((n : ℝ) + D + 1) ≤ Real.log ((n : ℝ) + 1) + Real.log ((D : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [← Real.log_mul (by positivity) (by positivity)]
  have hle : (n : ℝ) + D + 1 ≤ ((n : ℝ) + 1) * ((D : ℝ) + 1) := by nlinarith [mul_nonneg hn hD]
  first
    | exact Real.log_le_log (by positivity) hle
    | exact (Real.log_le_log_iff (by positivity) (by positivity)).mpr hle
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.log ((D : ℝ) + 1) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact Real.log_nonneg (by linarith)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = c₀ / Real.log 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact div_nonneg hc0 hl2.le
  have hcL : ∀ t : ℝ, Real.log 2 ≤ t → c₀ ≤ L * t := by
    intro t ht
    have e : c₀ = L * Real.log 2 := by
      rw [hL]
      first
        | exact (div_mul_cancel₀ c₀ hl2.ne').symm
        | field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left ht hL0
  refine ⟨(1 / 2) * (2 ^ D + 3 ^ D * (2 + (D : ℝ))) * (1 + L), fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ t : ℝ, t = Real.log ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hℓ2 : Real.log 2 ≤ ℓ := by
    rw [hℓ]
    first
      | exact Real.log_le_log (by norm_num) (by linarith)
      | exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr (by linarith)
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hc : c₀ ≤ L * ℓ := hcL ℓ hℓ2
  have hlogND : Real.log ((n : ℝ) + D + 1) ≤ ℓ + c₀ := by
    rw [hℓ, hc₀]
    exact log_add_add_one_le_log_add_log n D
  have hX : 0 ≤ (1 + L) * ℓ := mul_nonneg (by linarith) hℓ0
  have hS1 : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1))
      ≤ 2 ^ D * (n : ℝ) ^ D * ((1 + L) * ℓ) := by
    have h1 : ∀ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n,
        -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ≤ (1 + L) * ℓ := by
      intro a ha
      have := (chiPAux_neg_log_step_mem D n a ha).2
      linarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hcard : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ 2 ^ D * (n : ℝ) ^ D := by
      have h3 : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ ((n : ℝ) + 1) ^ D := by
        exact_mod_cast chiPAux_card_adt_le D n
      have h4 : ((n : ℝ) + 1) ^ D ≤ (2 * (n : ℝ)) ^ D := by
        gcongr
        linarith
      rw [mul_pow] at h4
      linarith
    exact h2.trans (mul_le_mul_of_nonneg_right hcard hX)
  have hS2 : ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ 3 ^ D * (2 + (D : ℝ)) * ((1 + L) * ℓ) * (n : ℝ) ^ D := by
    apply chiPAux_sum_filter_zero_le D n hn ((1 + L) * ℓ) hX
    intro b hb
    have hs := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1
    have h1 := chiPAux_neg_log_monoNormSq_le b
    rw [hs] at h1
    push_cast at h1
    have e : (n : ℝ) + 1 + D = (n : ℝ) + D + 1 := by ring
    rw [e, ← hc₀] at h1
    have h2 : (D : ℝ) * Real.log ((n : ℝ) + D + 1) ≤ D * (ℓ + c₀) := mul_le_mul_of_nonneg_left hlogND hD0
    have h3 : ((n : ℝ) + 1) * c₀ ≤ ((n : ℝ) + 1) * (L * ℓ) := mul_le_mul_of_nonneg_left hc (by linarith)
    have h4 : (D : ℝ) * c₀ ≤ D * (L * ℓ) := mul_le_mul_of_nonneg_left hc hD0
    have hLl : 0 ≤ L * ℓ := mul_nonneg hL0 hℓ0
    have h5 : 0 ≤ ((n : ℝ) - 1) * (L * ℓ) := mul_nonneg (by linarith) hLl
    have h6 : 0 ≤ (D : ℝ) * ℓ * ((n : ℝ) - 1) := mul_nonneg (mul_nonneg hD0 hℓ0) (by linarith)
    have h7 : 0 ≤ (D : ℝ) * (L * ℓ) * ((n : ℝ) - 1) := mul_nonneg (mul_nonneg hD0 hLl) (by linarith)
    have h8 : 0 ≤ (n : ℝ) * ℓ := mul_nonneg hn0 hℓ0
    linarith
  rw [chiP_succ_sub_eq, ← hℓ]
  calc _ ≤ (1 / 2) * (2 ^ D * (n : ℝ) ^ D * ((1 + L) * ℓ)
          + 3 ^ D * (2 + (D : ℝ)) * ((1 + L) * ℓ) * (n : ℝ) ^ D) := by linarith
    _ = (1 / 2) * (2 ^ D + 3 ^ D * (2 + (D : ℝ))) * (1 + L) * (n : ℝ) ^ D * ℓ := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
