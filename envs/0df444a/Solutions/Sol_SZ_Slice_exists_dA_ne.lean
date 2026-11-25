-- Prove2me | solution 1 for SZ.Slice.exists_dA_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:44:04.348154+00:00
-- url     : https://prove2.me/submissions/aa3f6f37-fb6a-4e8b-a054-bc47319c7bf8

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_eq_fixed_of_trapped
import Theorems.Thm_SZ_Slice_U_eq_one_add
import Theorems.Thm_SZ_Slice_form_a
import Theorems.Thm_SZ_Slice_W_ne_val
import Theorems.Thm_SZ_Slice_W_mem
import Theorems.Thm_SZ_Slice_W_succ
import Theorems.Thm_SZ_Slice_asel_eq_zero
import Theorems.Thm_SZ_Slice_asel_lt
import Theorems.Thm_SZ_Slice_bsel_le
import Theorems.Thm_SZ_Slice_dA_eq
import Theorems.Thm_SZ_Slice_dB_eq
import Theorems.Thm_SZ_Slice_e_pos
import Theorems.Thm_SZ_Slice_lt_bsel_add
import Theorems.Thm_SZ_Slice_m_sub_one_ne
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_SZ_Slice_val_pick_W


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ}
    (hk : 1 ≤ k₀) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (N : ℕ) :
    ∃ k, N ≤ k ∧ S.dA (S.w0 j k₀) k ≠ S.e := by
  by_contra hcon
  push Not at hcon
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hm1 : (1 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hU := U_eq_one_add he
  have hfa := form_a he hpsq
  have hecast : (S.e : ℝ) = (S.m : ℝ) - 1 := by rw [he]; push_cast; ring
  -- the `b`-digit is forced to `e` as well
  have hbe : ∀ k, N ≤ k → S.dB (S.w0 j k₀) k = S.e := by
    intro k hkN
    by_contra hb
    have hblt : S.bsel (S.W (S.w0 j k₀) k) < S.e :=
      lt_of_le_of_ne (S.bsel_le _) (by rw [dB_eq] at hb; exact hb)
    have hmax := S.lt_bsel_add hblt
    have hexp : ((S.bsel (S.W (S.w0 j k₀) k) : ℝ) + (S.p : ℝ)) * S.sq
        = (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq + (S.p : ℝ) * S.sq := by ring
    rw [hexp] at hmax
    have hv : S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq
        < (S.p : ℝ) * S.sq := by linarith
    have ha : (S.dA (S.w0 j k₀) k : ℝ) < (S.e : ℝ) := by
      rcases le_or_gt (S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq) S.U with
        hle | hlt
      · rw [dA_eq, S.asel_eq_zero hle]
        have := S.e_pos
        exact_mod_cast this
      · have hal := S.asel_lt hlt
        rw [dA_eq]
        linarith
    rw [hcon k hkN] at ha
    exact lt_irrefl _ ha
  -- from `N` on the dynamics is one affine map
  have hrec : ∀ k, N ≤ k → S.W (S.w0 j k₀) (k + 1)
      = (S.m : ℝ) * S.W (S.w0 j k₀) k - (S.m : ℝ) * ((S.m : ℝ) - 1) * S.U := by
    intro k hkN
    rw [W_succ, val_pick_W, hcon k hkN, hbe k hkN, hecast, hU]
    ring
  have hfix : ((S.m : ℝ) * ((S.m : ℝ) - 1) * S.U) / ((S.m : ℝ) - 1) = (S.m : ℝ) * S.U := by
    have hne := S.m_sub_one_ne
    field_simp
  have hbd : ∀ k, N ≤ k →
      |S.W (S.w0 j k₀) k - ((S.m : ℝ) * ((S.m : ℝ) - 1) * S.U) / ((S.m : ℝ) - 1)|
        ≤ (S.m : ℝ) * S.U := by
    intro k _
    rw [hfix]
    obtain ⟨hlo, hhi⟩ := W_mem hw0 hw1 k
    rw [abs_le]
    constructor <;> linarith
  have hfixed := eq_fixed_of_trapped (f := S.W (S.w0 j k₀)) (r := (S.m : ℝ))
    (c := (S.m : ℝ) * ((S.m : ℝ) - 1) * S.U) (D := (S.m : ℝ) * S.U) hm1 hrec hbd
  rw [hfix] at hfixed
  have hval : (S.m : ℝ) * S.U = (((S.m : ℤ)) : ℝ) + (((S.m : ℤ)) : ℝ) * S.sq := by
    rw [hU]; push_cast; ring
  exact W_ne_val he hk h0 h1 N (le_refl _) (by rw [hfixed, hval])
end SZ.Slice
