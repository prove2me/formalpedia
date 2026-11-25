-- Prove2me | solution 1 for SZ.Slice.exists_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:25.286442+00:00
-- url     : https://prove2.me/submissions/84933a45-4894-4c55-a148-ccd8b62e00ac

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_one_lt_sq
import Theorems.Thm_SZ_Slice_sq_pos
import Theorems.Thm_SZ_Slice_irrational_sq
import Theorems.Thm_SZ_Slice_p_pos
import Theorems.Thm_SZ_Slice_p_cast_pos
import Theorems.Thm_SZ_Slice_M_mul
import Theorems.Thm_SZ_Slice_M_le_one
import Theorems.Thm_SZ_Slice_M_pos
import Theorems.Thm_SZ_Slice_U_eq

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) {k₀ : ℤ} (hk : 1 ≤ k₀) :
    ∃ j : ℤ, 1 ≤ j ∧ 0 < S.sigma j k₀ ∧ S.sigma j k₀ < S.U := by
  have hp := S.p_cast_pos
  have hsq := S.sq_pos
  have h1sq := S.one_lt_sq
  have hM1 := S.M_le_one
  have hMpos := S.M_pos
  have hk1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
  set T : ℝ := ((S.p : ℝ) * (k₀ : ℝ) + S.M) * S.sq with hT
  -- `T - U = p k₀ √m - M`
  have hTU : T - S.U = (S.p : ℝ) * (k₀ : ℝ) * S.sq - S.M := by
    rw [hT, S.U_eq]; ring
  have hp2 : (2 : ℝ) ≤ (S.p : ℝ) := by exact_mod_cast S.two_le_p
  have hTUpos : 0 < T - S.U := by
    rw [hTU]
    have hkpos : (0 : ℝ) < (k₀ : ℝ) := by linarith
    have hpk : (2 : ℝ) ≤ (S.p : ℝ) * (k₀ : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (S.p : ℝ) - 2)
        (by linarith : (0:ℝ) ≤ (k₀ : ℝ) - 1)]
    nlinarith
  refine ⟨⌈(T - S.U) / (S.p : ℝ)⌉, ?_, ?_, ?_⟩
  · -- `j > (T-U)/p > 0`
    have h := Int.le_ceil ((T - S.U) / (S.p : ℝ))
    have hdiv : 0 < (T - S.U) / (S.p : ℝ) := div_pos hTUpos hp
    have : (0 : ℝ) < (⌈(T - S.U) / (S.p : ℝ)⌉ : ℝ) := lt_of_lt_of_le hdiv h
    have h0 : (0 : ℤ) < ⌈(T - S.U) / (S.p : ℝ)⌉ := by exact_mod_cast this
    omega
  · -- `p j < T`, since `⌈x⌉ < x + 1` and `(T-U)/p + 1 ≤ T/p`
    have hlt : (⌈(T - S.U) / (S.p : ℝ)⌉ : ℝ) < (T - S.U) / (S.p : ℝ) + 1 :=
      Int.ceil_lt_add_one _
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hcancel : (S.p : ℝ) * ((T - S.U) / (S.p : ℝ) + 1) = T - S.U + (S.p : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    have hU := S.p_le_U
    rw [sigma, ← hT]
    linarith
  · -- `p j > T - U`: `⌈x⌉ ≥ x`, and equality is impossible by irrationality
    have hge : (T - S.U) / (S.p : ℝ) ≤ (⌈(T - S.U) / (S.p : ℝ)⌉ : ℝ) := Int.le_ceil _
    have hmul := mul_le_mul_of_nonneg_left hge hp.le
    have hcancel : (S.p : ℝ) * ((T - S.U) / (S.p : ℝ)) = T - S.U := by field_simp
    rw [hcancel] at hmul
    rcases lt_or_eq_of_le hmul with hlt | heq
    · rw [sigma, ← hT]; linarith
    · -- `p j = p k₀ √m - M` would make `√m` rational
      exfalso
      set j : ℤ := ⌈(T - S.U) / (S.p : ℝ)⌉
      have hMval : ((S.m : ℝ) - 1) * S.M = (S.e : ℝ) := S.M_mul
      have hkey : (((S.m : ℤ) - 1) * S.p * k₀ : ℤ) * S.sq
          = (((S.m : ℤ) - 1) * S.p * j + S.e : ℤ) := by
        have hexp : ((S.m : ℝ) - 1) * ((S.p : ℝ) * (j : ℝ))
            = ((S.m : ℝ) - 1) * ((S.p : ℝ) * (k₀ : ℝ) * S.sq - S.M) := by
          rw [← hTU]; rw [heq]
        push_cast
        nlinarith [hMval, hexp]
      have hne : (((S.m : ℤ) - 1) * S.p * k₀ : ℤ) ≠ 0 := by
        have hm3 : (3 : ℤ) ≤ (S.m : ℤ) := by exact_mod_cast S.three_le
        have hp0 := S.p_pos
        exact mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
      exact (S.irrational_sq.intCast_mul hne).ne_int _ hkey
end SZ.Slice
