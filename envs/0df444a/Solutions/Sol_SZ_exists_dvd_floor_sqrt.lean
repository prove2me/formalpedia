-- Prove2me | solution 1 for SZ.exists_dvd_floor_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:35.456635+00:00
-- url     : https://prove2.me/submissions/17a5bb4d-a8d0-4a09-bd2b-85ad84139aff

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
import Theorems.Thm_SZ_Slice_dvd_floor_of_e_le
import Theorems.Thm_SZ_Slice_dvd_floor_of_uniform
import Theorems.Thm_SZ_Slice_exists_translate


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hcase : (p ∣ (m : ℤ) - 1 ∧ p ^ 2 ≤ (m : ℤ)) ∨
      (p ∣ (m : ℤ) ∧ (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m))) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → p ∣ ⌊ξ * Real.sqrt m ^ n⌋ := by
  rcases hcase with ⟨hd, hpm⟩ | ⟨hd, hU⟩
  · -- branch (i): the uniform alphabet, hygiene from `√m ≥ p`
    set S : Slice := sliceOne p m hp hm hns hd hpm with hS
    obtain ⟨j, hj, h0, h1⟩ := S.exists_translate (k₀ := 1) le_rfl
    have hpsq : (S.p : ℝ) ≤ S.sq := by
      simp only [Slice.sq, hS, sliceOne]
      exact p_le_sqrt (show (0:ℤ) ≤ p by omega) hpm
    exact Slice.dvd_floor_of_uniform S rfl hpsq hj le_rfl h0.le h1.le
  · -- branch (ii): `e = m - p ≤ m - 2`, hygiene free
    set S : Slice := sliceTwo p m hp hm hns hd hU with hS
    obtain ⟨j, hj, h0, h1⟩ := S.exists_translate (k₀ := 1) le_rfl
    have he : S.e ≤ (S.m : ℤ) - 2 := by
      simp only [hS, sliceTwo]
      omega
    exact Slice.dvd_floor_of_e_le S he hj h0.le h1.le
end SZ
