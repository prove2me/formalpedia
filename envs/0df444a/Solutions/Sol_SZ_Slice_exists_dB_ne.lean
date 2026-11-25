-- Prove2me | solution 1 for SZ.Slice.exists_dB_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:46:31.648818+00:00
-- url     : https://prove2.me/submissions/bd4eca70-9dc7-4625-b7c7-1db491c6fd57

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_U_eq_one_add
import Theorems.Thm_SZ_Slice_form_b
import Theorems.Thm_SZ_Slice_W_ne_val
import Theorems.Thm_SZ_Slice_W_mem
import Theorems.Thm_SZ_Slice_W_succ
import Theorems.Thm_SZ_Slice_asel_eq_zero
import Theorems.Thm_SZ_Slice_asel_lt
import Theorems.Thm_SZ_Slice_bsel_eq_zero_iff
import Theorems.Thm_SZ_Slice_dA_eq
import Theorems.Thm_SZ_Slice_dB_eq
import Theorems.Thm_SZ_Slice_p_cast_pos
import Theorems.Thm_SZ_Slice_sq_pos
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_SZ_Slice_val_pick_W


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ}
    (hk : 1 ≤ k₀) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (N : ℕ) :
    ∃ k, N ≤ k ∧ S.dB (S.w0 j k₀) k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hm1 : (1 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hU := U_eq_one_add he
  have hsqpos := S.sq_pos
  have hppos := S.p_cast_pos
  -- the state stays in `L = [0, p√m)`
  have hltL : ∀ k, N ≤ k → S.W (S.w0 j k₀) k < (S.p : ℝ) * S.sq := by
    intro k hkN
    refine (S.bsel_eq_zero_iff (W_mem hw0 hw1 k).1).mp ?_
    rw [← dB_eq]
    exact hcon k hkN
  -- one step from above the window overshoots
  have hover : (S.p : ℝ) * S.sq ≤ (S.m : ℝ) * (S.U - (S.p : ℝ)) := form_b he hpsq
  by_cases hcase : ∃ k, N ≤ k ∧ S.U < S.W (S.w0 j k₀) k
  · obtain ⟨k, hkN, hkU⟩ := hcase
    have hb0 : S.bsel (S.W (S.w0 j k₀) k) = 0 := by rw [← dB_eq]; exact hcon k hkN
    have hv : S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq
        = S.W (S.w0 j k₀) k := by rw [hb0]; push_cast; ring
    have halt : (S.dA (S.w0 j k₀) k : ℝ) < S.W (S.w0 j k₀) k - S.U + (S.p : ℝ) := by
      have := S.asel_lt (w := S.W (S.w0 j k₀) k) (by rw [hv]; exact hkU)
      rw [hv] at this
      rw [dA_eq]
      exact this
    have hstep : S.W (S.w0 j k₀) (k + 1)
        = (S.m : ℝ) * (S.W (S.w0 j k₀) k - (S.dA (S.w0 j k₀) k : ℝ)) := by
      rw [W_succ, val_pick_W, hcon k hkN]
      push_cast
      ring
    have hnext := hltL (k + 1) (by omega)
    rw [hstep] at hnext
    nlinarith [mul_lt_mul_of_pos_left halt hmr]
  · push Not at hcase
    have hmul : ∀ k, N ≤ k → S.W (S.w0 j k₀) (k + 1) = (S.m : ℝ) * S.W (S.w0 j k₀) k := by
      intro k hkN
      have hb0 : S.bsel (S.W (S.w0 j k₀) k) = 0 := by rw [← dB_eq]; exact hcon k hkN
      have hv : S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq
          = S.W (S.w0 j k₀) k := by rw [hb0]; push_cast; ring
      have ha0 : S.dA (S.w0 j k₀) k = 0 := by
        rw [dA_eq]
        exact S.asel_eq_zero (by rw [hv]; exact hcase k hkN)
      rw [W_succ, val_pick_W, ha0, hcon k hkN]
      push_cast
      ring
    have hpow : ∀ n : ℕ, S.W (S.w0 j k₀) (N + n) = (S.m : ℝ) ^ n * S.W (S.w0 j k₀) N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : N + (n + 1) = (N + n) + 1 := by omega
        rw [e, hmul (N + n) (Nat.le_add_right _ _), ih, pow_succ]
        ring
    have hne0 : S.W (S.w0 j k₀) N ≠ 0 := by
      have h := W_ne_val he hk h0 h1 N (p := 0) (q := 0) (by omega)
      simpa using h
    have hpos : 0 < S.W (S.w0 j k₀) N :=
      lt_of_le_of_ne (W_mem hw0 hw1 N).1 (Ne.symm hne0)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((S.p : ℝ) * S.sq / S.W (S.w0 j k₀) N) hm1
    have hlt := hltL (N + n) (Nat.le_add_right _ _)
    rw [hpow n] at hlt
    have := (div_lt_iff₀ hpos).mp hn
    nlinarith
end SZ.Slice
