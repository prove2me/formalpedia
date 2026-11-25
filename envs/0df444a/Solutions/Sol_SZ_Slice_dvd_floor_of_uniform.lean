-- Prove2me | solution 1 for SZ.Slice.dvd_floor_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:11.837037+00:00
-- url     : https://prove2.me/submissions/59101255-f651-45ca-9922-050bb5ba383d

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_exists_dA_ne
import Theorems.Thm_SZ_Slice_exists_dB_ne
import Theorems.Thm_SZ_Slice_dA_mem
import Theorems.Thm_SZ_Slice_dB_mem
import Theorems.Thm_SZ_Slice_dvd_floor_of_hygiene
import Theorems.Thm_SZ_Slice_p_pos
import Theorems.Thm_SZ_Slice_three_le_cast


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (he : S.e = (S.m : ℤ) - 1)
    (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ} (hj : 1 ≤ j) (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hple : S.p ≤ (S.m : ℤ) - 1 := le_trans S.p_le_e (by omega)
  refine dvd_floor_of_hygiene S hj h0 h1 (fun N => ?_) (fun N => ?_)
  · obtain ⟨k, hkN, hne⟩ := exists_dA_ne he hpsq hk h0 h1 N
    have hle := (dA_mem hw0 hw1 k).2.2
    obtain ⟨r, hr⟩ := (dA_mem hw0 hw1 k).1
    obtain ⟨t, ht⟩ := S.p_dvd_e
    have hlt : S.dA (S.w0 j k₀) k < S.e := lt_of_le_of_ne hle hne
    have h4 : S.p * r < S.p * t := by rw [← hr, ← ht]; exact hlt
    have h5 : r < t := lt_of_mul_lt_mul_left h4 S.p_pos.le
    have h6 : S.dA (S.w0 j k₀) k ≤ S.e - S.p := by
      calc S.dA (S.w0 j k₀) k = S.p * r := hr
        _ ≤ S.p * (t - 1) := mul_le_mul_of_nonneg_left (by omega) S.p_pos.le
        _ = S.p * t - S.p := by ring
        _ = S.e - S.p := by rw [← ht]
    exact ⟨k, hkN, by omega⟩
  · obtain ⟨k, hkN, hne⟩ := exists_dB_ne he hpsq hk h0 h1 N
    have hge := (dB_mem hw0 hw1 k).2.1
    obtain ⟨r, hr⟩ := (dB_mem hw0 hw1 k).1
    have hr0 : 0 < r := by
      rcases lt_trichotomy r 0 with h | h | h
      · exfalso; nlinarith [S.p_pos]
      · exact absurd (by rw [hr, h, mul_zero]) hne
      · exact h
    have h6 : S.p ≤ S.dB (S.w0 j k₀) k := by
      calc S.p = S.p * 1 := (mul_one _).symm
        _ ≤ S.p * r := mul_le_mul_of_nonneg_left (by omega) S.p_pos.le
        _ = S.dB (S.w0 j k₀) k := hr.symm
    have hle := (dB_mem hw0 hw1 k).2.2
    exact ⟨k, hkN, by omega⟩
end SZ.Slice
