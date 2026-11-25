-- Prove2me | solution 1 for SZ.Slice.stt_snd_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:34:02.669846+00:00
-- url     : https://prove2.me/submissions/8d9b1a08-566d-48dc-9d5f-b0b698fae9d5

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_stt_zero
import Theorems.Thm_SZ_Slice_stt_succ
import Theorems.Thm_SZ_Slice_dB_mem
import Theorems.Thm_SZ_Slice_p_pos
import Theorems.Thm_SZ_Slice_three_le_cast


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) {j k₀ : ℤ} (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (k : ℕ) :
    S.p * (S.m : ℤ) ^ (k + 1) + (S.m : ℤ) ≤ (stt S j k₀ k).2 := by
  have hmz : (3 : ℤ) ≤ (S.m : ℤ) := by exact_mod_cast S.three_le
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hppos := S.p_pos
  induction k with
  | zero =>
    have hd : (0 : ℤ) ≤ (S.m : ℤ) * (S.p * (k₀ - 1)) :=
      mul_nonneg (by omega) (mul_nonneg hppos.le (by omega))
    rw [stt_zero]
    simp only [pow_succ, pow_zero, one_mul]
    nlinarith [hd]
  | succ k ih =>
    rw [stt_succ]
    show S.p * (S.m : ℤ) ^ (k + 1 + 1) + (S.m : ℤ)
      ≤ (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k)
    have hb : S.dB (S.w0 j k₀) k ≤ S.e := (dB_mem hw0 hw1 k).2.2
    have hbe : S.dB (S.w0 j k₀) k ≤ (S.m : ℤ) - 1 := by rw [he] at hb; exact hb
    have hinner : S.p * (S.m : ℤ) ^ (k + 1) + 1
        ≤ (stt S j k₀ k).2 - S.dB (S.w0 j k₀) k := by linarith
    have hstep := mul_le_mul_of_nonneg_left hinner (by omega : (0 : ℤ) ≤ (S.m : ℤ))
    have hid : (S.m : ℤ) * (S.p * (S.m : ℤ) ^ (k + 1) + 1)
        = S.p * (S.m : ℤ) ^ (k + 1 + 1) + (S.m : ℤ) := by ring
    rw [hid] at hstep
    linarith
end SZ.Slice
